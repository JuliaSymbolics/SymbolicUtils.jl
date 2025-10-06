struct Substituter{Fold, D <: AbstractDict, F}
    dict::D
    filter::F
end

function (s::Substituter)(ex)
    return get(s.dict, ex, ex)
end

function (s::Substituter{Fold})(ex::BasicSymbolic{T}) where {T, Fold}
    result = get(s.dict, ex, nothing)
    result === nothing || return result
    iscall(ex) || return ex
    s.filter(ex) || return ex
    op = operation(ex)
    _op = s(op)

    args = arguments(ex)::ROArgsT{T}
    for i in eachindex(args)
        arg = args[i]
        newarg = s(arg)
        if arg === newarg || @manually_scope COMPARE_FULL => true isequal(arg, newarg)::Bool
            continue
        end
        if args isa ROArgsT{T}
            args = copy(parent(args))::ArgsT{T}
        end
        args[i] = Const{T}(newarg)
    end
    if args isa ArgsT{T} || _op !== op || Fold && all(isconst, args)
        if Fold
            return combine_fold(T, _op, args, metadata(ex))
        else
            return maketerm(BasicSymbolic{T}, _op, args, metadata(ex))
        end
    end
    return ex
end

function _const_or_not_symbolic(x)
    isconst(x) || !(x isa BasicSymbolic)
end

function combine_fold(::Type{T}, op, args::Union{ROArgsT{T}, ArgsT{T}}, meta) where {T}
    @nospecialize op args meta
    can_fold = !(op isa BasicSymbolic{T}) # && all(_const_or_not_symbolic, args)
    for arg in args
        can_fold &= _const_or_not_symbolic(arg)
        can_fold || break
    end
    if op === (+)
        add_worker(T, args)
    elseif op === (*)
        can_fold ? mapfoldl(unwrap_const, *, args) : mul_worker(T, args)
    elseif op === (/)
        can_fold ? Const{T}(unwrap_const(args[1]) / unwrap_const(args[2])) : (args[1] / args[2])
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

function default_substitute_filter(ex::BasicSymbolic{T}) where {T}
    iscall(ex) && !(operation(ex) isa Operator)
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
@inline function substitute(expr, dict; fold=true, filterer=default_substitute_filter)
    isempty(dict) && !fold && return expr
    return Substituter{fold, typeof(dict), typeof(filterer)}(dict, filterer)(expr)
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
        Prewalk(Substituter(dict))
    end
    rw(expr)
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
        BSImpl.ArrayOp(; expr = inner_expr, term) => begin
            query!(predicate, @something(term, inner_expr); recurse, default)
        end
    end
end

search_variables!(buffer, expr; kw...) = nothing

"""
    $(TYPEDSIGNATURES)

The default `is_atomic` predicate for [`search_variables!`](@ref). `ex` is considered
atomic if one of the following conditions is true:
- It is a `Sym` and not an internal index variable for an arrayop
- It is a `Term`, the operation is a `BasicSymbolic` and the operation represents a
  dependent variable according to [`is_function_symbolic`](@ref).
- It is a `Term`, the operation is `getindex` and the variable being indexed is atomic.
"""
function default_is_atomic(ex::BasicSymbolic{T}) where {T}
    @match ex begin
        BSImpl.Sym(; name) => name !== IDXS_SYM
        BSImpl.Term(; f) && if f isa Operator end => true
        BSImpl.Term(; f) && if f isa BasicSymbolic{T} end => !is_function_symbolic(f)
        BSImpl.Term(; f, args) && if f === getindex end => default_is_atomic(args[1])
        _ => false
    end
end

"""
    $(TYPEDSIGNATURES)

Find all variables used in `expr` and add them to `buffer`. A variable is identified by the
predicate `is_atomic`. The predicate `recurse` determines whether to search further inside
`expr` if it is not a variable. Note that `recurse` must at least return `false` if
`iscall` returns `false`.

Wrappers for [`BasicSymbolic`](@ref) should implement this function by unwrapping.

See also: [`default_is_atomic`](@ref).
"""
function search_variables!(buffer, expr::BasicSymbolic; is_atomic::F = default_is_atomic, recurse::G = iscall) where {F, G}
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
        BSImpl.ArrayOp(; expr = inner_expr, term) => begin
            search_variables!(buffer, @something(term, inner_expr); is_atomic, recurse)
        end
    end
    return nothing
end

_default_buffer(::BasicSymbolic{T}) where {T} = Set{BasicSymbolic{T}}()
_default_buffer(x::Any) = unwrap(x) === x ? Set() : _default_buffer(unwrap(x))

function search_variables(expr; kw...)
    buffer = _default_buffer(expr)
    search_variables!(buffer, expr; kw...)
    return buffer
end

struct ArrayOpReduceCache{T}
    new_ranges::RangesT{T}
    subrules::Dict{BasicSymbolic{T}, Int}
    collapsed_idxs::Set{BasicSymbolic{T}}
    collapsed_ranges::Vector{StepRange{Int, Int}}
end

function ArrayOpReduceCache{T}() where {T}
    ArrayOpReduceCache{T}(RangesT{T}(), Dict{BasicSymbolic{T}, Int}(), Set{BasicSymbolic{T}}(), StepRange{Int, Int}[])
end

function Base.empty!(x::ArrayOpReduceCache)
    empty!(x.new_ranges)
    empty!(x.subrules)
    empty!(x.collapsed_idxs)
    empty!(x.collapsed_ranges)
    return x
end

const ARRAYOP_REDUCE_SYMREAL = TaskLocalValue{ArrayOpReduceCache{SymReal}}(ArrayOpReduceCache{SymReal})
const ARRAYOP_REDUCE_SAFEREAL = TaskLocalValue{ArrayOpReduceCache{SafeReal}}(ArrayOpReduceCache{SafeReal})

arrayop_reduce_cache(::Type{SymReal}) = empty!(ARRAYOP_REDUCE_SYMREAL[])
arrayop_reduce_cache(::Type{SafeReal}) = empty!(ARRAYOP_REDUCE_SAFEREAL[])

function _reduce_eliminated_idxs(expr::BasicSymbolic{T}, output_idx::OutIdxT{T}, ranges::RangesT{T}, reduce) where {T}
    cache = arrayop_reduce_cache(T)
    new_ranges = cache.new_ranges
    subrules = cache.subrules
    new_expr = Code.unidealize_indices(expr, ranges, new_ranges)
    merge!(new_ranges, ranges)
    collapsed = cache.collapsed_idxs
    union!(collapsed, keys(new_ranges))
    setdiff!(collapsed, output_idx)
    collapsed_ranges = cache.collapsed_ranges
    for i in collapsed
        push!(collapsed_ranges, new_ranges[i])
    end
    return mapreduce(reduce, Iterators.product(collapsed_ranges...)) do iidxs
        for (idx, ii) in zip(iidxs, collapsed)
            subrules[ii] = idx
        end
        return substitute(new_expr, subrules; fold = false)
    end
end
@cache function reduce_eliminated_idxs_1(expr::BasicSymbolic{SymReal}, output_idx::OutIdxT{SymReal}, ranges::RangesT{SymReal}, reduce)::BasicSymbolic{SymReal}
    _reduce_eliminated_idxs(expr, output_idx, ranges, reduce)
end
@cache function reduce_eliminated_idxs_2(expr::BasicSymbolic{SafeReal}, output_idx::OutIdxT{SafeReal}, ranges::RangesT{SafeReal}, reduce)::BasicSymbolic{SafeReal}
    _reduce_eliminated_idxs(expr, output_idx, ranges, reduce)
end
function reduce_eliminated_idxs(expr::BasicSymbolic{T}, output_idx::OutIdxT{T}, ranges::RangesT{T}, reduce) where {T}
    if T === SymReal
        return reduce_eliminated_idxs_1(expr, output_idx, ranges, reduce)
    elseif T === SafeReal
        return reduce_eliminated_idxs_2(expr, output_idx, ranges, reduce)
    end
    _unreachable()
end

"""
    $(TYPEDSIGNATURES)

Given a function `f`, return a function that will scalarize an expression with `f` as the
head. The returned function is passed `f`, the expression with `f` as the head, and
`Val(true)` or `Val(false)` indicating whether to recursively scalarize or not.
"""
scalarization_function(@nospecialize(_)) = _default_scalarize

scalarization_function(::Union{typeof(+), typeof(-), typeof(*), typeof(/), typeof(\), typeof(^), typeof(LinearAlgebra.norm), typeof(map), typeof(mapreduce), typeof(broadcast), typeof(adjoint)}) = _default_scalarize_array

function _default_scalarize_array(f, x::BasicSymbolic{T}, ::Val{toplevel}) where {T, toplevel}
    @nospecialize f
    args = arguments(x)
    if toplevel && f !== broadcast
        f(map(unwrap_const, args)...)
    else
        f(map(unwrap_const ∘ scalarize, args)...)
    end
end

function _default_scalarize(f, x::BasicSymbolic{T}, ::Val{toplevel}) where {T, toplevel}
    @nospecialize f

    sh = shape(x)
    is_array_shape(sh) && return [x[idx] for idx in eachindex(x)]

    args = arguments(x)
    if toplevel
        f(map(unwrap_const, args)...)
    else
        f(map(unwrap_const ∘ scalarize, args)...)
    end
end

function scalarize(x::BasicSymbolic{T}, ::Val{toplevel} = Val{false}()) where {T, toplevel}
    sh = shape(x)
    sh isa Unknown && return x
    @match x begin
        BSImpl.Const(;) => return x
        BSImpl.Sym(;) => is_array_shape(sh) ? [x[idx] for idx in eachindex(x)] : x
        BSImpl.ArrayOp(; output_idx, expr, term, ranges, reduce) => begin
            term === nothing || return scalarize(term, Val{toplevel}())
            subrules = Dict()
            new_expr = reduce_eliminated_idxs(expr, output_idx, ranges, reduce)
            empty!(subrules)
            map(Iterators.product(sh...)) do idxs
                for (i, ii) in enumerate(output_idx)
                    ii isa Int && continue
                    subrules[ii] = idxs[i]
                end
                if toplevel
                    substitute(new_expr, subrules; fold = true)
                else
                    scalarize(substitute(new_expr, subrules; fold = true))
                end
            end
        end
        _ => begin
            f = operation(x)
            f isa BasicSymbolic{T} && return length(sh) == 0 ? x : [x[idx] for idx in eachindex(x)]
            return scalarization_function(f)(f, x, Val{toplevel}())
        end
    end
end
function scalarize(arr::AbstractArray, ::Val{toplevel} = Val{false}()) where {toplevel}
    map(Base.Fix2(scalarize, Val{toplevel}()), arr)
end
scalarize(x, _...) = x

scalarization_function(::typeof(inv)) = _inv_scal

function _inv_scal(::typeof(inv), x::BasicSymbolic{T}, ::Val{toplevel}) where {T, toplevel}
    sh = shape(x)
    (sh isa ShapeVecT && !isempty(sh)) ? [x[idx] for idx in eachindex(x)] : x
end

scalarization_function(::typeof(LinearAlgebra.det)) = _det_scal

function _det_scal(::typeof(LinearAlgebra.det), x::BasicSymbolic{T}, ::Val{toplevel}) where {T, toplevel}
    arg = arguments(x)[1]
    sh = shape(arg)
    sh isa Unknown && return collect(x)
    sh = sh::ShapeVecT
    isempty(sh) && return x
    sarg = toplevel ? collect(arg) : scalarize(arg)
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

scalarization_function(::typeof(getindex)) = _getindex_scal

function _getindex_scal(::typeof(getindex), x::BasicSymbolic{T}, ::Val{toplevel}) where {T, toplevel}
    sh = shape(x)
    if length(sh) > 0
        return [x[idx] for idx in eachindex(x)]
    end
    args = arguments(x)
    return getindex(scalarize(args[1]), Iterators.drop(args, 1)...)
end
