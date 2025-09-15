struct Substituter{D <: AbstractDict, F}
    dict::D
    filterer::F
end

function (s::Substituter)(expr)
    s.filterer(expr) ? get(s.dict, expr, expr) : expr
end

function _const_or_not_symbolic(x)
    isconst(x) || !(x isa BasicSymbolic)
end

function combine_fold(::Type{BasicSymbolic{T}}, op, args::ArgsT{T}, meta) where {T}
    @nospecialize op args meta
    can_fold = !(op isa BasicSymbolic{T}) # && all(_const_or_not_symbolic, args)
    for arg in args
        can_fold &= _const_or_not_symbolic(arg)
        can_fold || break
    end
    if op === (+)
        add_worker(T, args)
    elseif op === (*)
        mul_worker(T, args)
    elseif op === (/)
        args[1] / args[2]
    elseif op === (^)
        args[1] ^ args[2]
    elseif can_fold
        if length(args) == 1
            Const{T}(op(unwrap_const(args[1])))
        elseif length(args) == 2
            Const{T}(op(unwrap_const(args[1]), unwrap_const(args[2])))
        elseif length(args) == 3
            Const{T}(op(unwrap_const(args[1]), unwrap_const(args[2]), unwrap_const(args[3])))
        else
            Const{T}(op(unwrap_const.(args)...))
        end
    else
        maketerm(BasicSymbolic{T}, op, args, meta)::BasicSymbolic{T}
    end
end

"""
    substitute(expr, dict; fold=true)

substitute any subexpression that matches a key in `dict` with
the corresponding value. If `fold=false`,
expressions which can be evaluated won't be evaluated.

```julia
julia> substitute(1+sqrt(y), Dict(y => 2), fold=true)
2.414213562373095
julia> substitute(1+sqrt(y), Dict(y => 2), fold=false)
1 + sqrt(2)
```
"""
@inline function substitute(expr, dict; fold=true, filterer=Returns(true))
    rw = if fold
        Prewalk(Substituter(dict, filterer); maketerm = combine_fold)
    else
        Prewalk(Substituter(dict, filterer))
    end
    rw(expr)
end

function substitute(expr::SparseMatrixCSC, subs; kw...)
    I, J, V = findnz(expr)
    V = substitute(V, subs; kw...)
    m, n = size(expr)
    return sparse(I, J, V, m, n)
end

@inline function substitute(expr::AbstractArray, dict; kw...)
    if _is_array_of_symbolics(expr)
        [substitute(x, dict; kw...) for x in expr]
    else
        expr
    end
end

"""
    occursin(needle::BasicSymbolic, haystack::BasicSymbolic)

Determine whether the second argument contains the first argument. Note that
this function doesn't handle associativity, commutativity, or distributivity.
"""
Base.occursin(needle::BasicSymbolic, haystack::BasicSymbolic) = _occursin(needle, haystack)
Base.occursin(needle, haystack::BasicSymbolic) = _occursin(needle, haystack)
Base.occursin(needle::BasicSymbolic, haystack) = _occursin(needle, haystack)
function _occursin(needle, haystack)
    isequal(unwrap_const(needle), unwrap_const(haystack)) && return true
    if iscall(haystack)
        args = arguments(haystack)
        for arg in args
            arg = unwrap_const(arg)
            if needle isa Integer || needle isa AbstractFloat
                isequal(needle, arg) && return true
            else
               occursin(needle, arg) && return true
            end
        end
    end
    return false
end

function query!(predicate::F, expr::BasicSymbolic; recurse::G = iscall, default::Bool = false) where {F, G}
    predicate(expr) && return true
    recurse(expr) || return default

    @match expr begin
        BSImpl.Term(; f, args) => any(args) do arg
            query!(predicate, arg; recurse, default)
        end
        BSImpl.AddMul(; dict) => any(keys(dict)) do arg
            query!(predicate, arg; recurse, default)
        end
        BSImpl.Div(; num, den) => query!(predicate, num; recurse, default) || query!(predicate, den; recurse, default)
    end
end

search_variables!(buffer, expr; kw...) = nothing

function search_variables!(buffer, expr::BasicSymbolic; is_atomic::F = issym, recurse::G = iscall) where {F, G}
    if is_atomic(expr)
        push!(buffer, expr)
        return
    end
    recurse(expr) || return
    @match expr begin
        BSImpl.Term(; f, args) => begin
            search_variables!(buffer, f; is_atomic, recurse)
            for arg in args
                search_variables!(buffer, arg; is_atomic, recurse)
            end
        end
        BSImpl.AddMul(; dict) => begin
            for k in keys(dict)
                search_variables!(buffer, k; is_atomic, recurse)
            end
        end
        BSImpl.Div(; num, den) => begin
            search_variables!(buffer, num; is_atomic, recurse)
            search_variables!(buffer, den; is_atomic, recurse)
        end
    end
    return nothing
end

function reduce_eliminated_idxs(expr::BasicSymbolic{T}, output_idx::OutIdxT{T}, ranges::RangesT{T}, reduce; subrules = Dict()) where {T}
    new_ranges = RangesT{T}()
    new_expr = Code.unidealize_indices(expr, ranges, new_ranges)
    merge!(new_ranges, ranges)
    collapsed = setdiff(collect(keys(new_ranges)), output_idx)
    collapsed_ranges = [new_ranges[k] for k in collapsed]
    return mapreduce(reduce, Iterators.product(collapsed_ranges...)) do iidxs
        for (idx, ii) in zip(iidxs, collapsed)
            subrules[ii] = idx
        end
        return substitute(new_expr, subrules; fold = true)
    end
    
end

"""
    $(TYPEDSIGNATURES)

Given a function `f`, return a function that will scalarize an expression with `f` as the
head. The returned function is passed `f` and the expression with `f` as the head.
"""
scalarization_function(@nospecialize(_)) = _default_scalarize

function _default_scalarize(f, x::BasicSymbolic{T}) where {T}
    @nospecialize f

    f isa BasicSymbolic{T} && return collect(x)

    args = arguments(x)
    f(map(unwrap_const ∘ scalarize, args)...)
end

function scalarize(x::BasicSymbolic{T}) where {T}
    sh = shape(x)
    sh isa Unknown && return x
    @match x begin
        BSImpl.Const(; val) => _is_array_shape(sh) ? Const{T}.(val) : x
        BSImpl.Sym(;) => _is_array_shape(sh) ? collect(x) : x
        BSImpl.ArrayOp(; output_idx, expr, term, ranges, reduce) => begin
            term === nothing || return scalarize(term)
            subrules = Dict()
            new_expr = reduce_eliminated_idxs(expr, output_idx, ranges, reduce; subrules)
            empty!(subrules)
            map(Iterators.product(sh...)) do idxs
                for (i, ii) in enumerate(output_idx)
                    ii isa Int && continue
                    subrules[ii] = idxs[i]
                end
                scalarize(substitute(new_expr, subrules; fold = true))
            end
        end
        _ => begin
            f = operation(x)
            f isa BasicSymbolic{T} && return collect(x)
            return scalarization_function(f)(f, x)
        end
    end
end
scalarize(arr::Array) = map(scalarize, arr)

scalarization_function(::typeof(inv)) = _inv_scal

function _inv_scal(::typeof(inv), x::BasicSymbolic{T}) where {T}
    sh = shape(x)
    (sh isa ShapeVecT && !isempty(sh)) ? collect(x) : x
end

scalarization_function(::typeof(LinearAlgebra.det)) = _det_scal

function _det_scal(::typeof(LinearAlgebra.det), x::BasicSymbolic{T}) where {T}
    arg = arguments(x)[1]
    sh = shape(arg)
    sh isa Unknown && return collect(x)
    sh = sh::ShapeVecT
    isempty(sh) && return x
    sarg = scalarize(arg)
    _det_scal(LinearAlgebra.det, T, sarg)
end

function _det_scal(::typeof(LinearAlgebra.det), ::Type{T}, x::AbstractMatrix) where {T}
    length(x) == 1 && return x[]
    add_buffer = BasicSymbolic{T}[]
    for i in 1:size(x, 1)
        ex = _det_scal(LinearAlgebra.det, T, view(x, setdiff(axes(x, 1), i), 2:size(x, 2)))
        push!(add_buffer, (isodd(i) ? 1 : -1) * x[i, 1] * ex)
    end
    return add_worker(T, add_buffer)
end
