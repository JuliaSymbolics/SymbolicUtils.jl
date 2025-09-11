struct Substituter{D <: AbstractDict}
    dict::D
end

function (s::Substituter)(expr)
    get(s.dict, expr, expr)
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
@inline function substitute(expr, dict; fold=true)
    rw = if fold
        Prewalk(Substituter(dict); maketerm = combine_fold)
    else
        Prewalk(Substituter(dict))
    end
    rw(expr)
end

@inline function substitute(expr::AbstractArray, dict; fold=true)
    if _is_array_of_symbolics(expr)
        [substitute(x, dict; fold) for x in expr]
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
