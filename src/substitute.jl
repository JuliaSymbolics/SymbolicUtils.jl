struct Substituter{D <: AbstractDict}
    dict::D
end

function (s::Substituter)(expr)
    get(s.dict, expr, expr)
end

function _const_or_not_symbolic(x)
    isconst(x) || !(x isa Symbolic)
end

function combine_fold(::Type{T}, op, args::ArgsT, meta) where {T}
    @nospecialize op args meta
    can_fold = !(op isa Symbolic) && all(_const_or_not_symbolic, args)
    if can_fold
        if op === (+)
            add_worker(args)
        elseif op === (*)
            mul_worker(args)
        elseif op === (/)
            args[1] / args[2]
        elseif op === (^)
            args[1] ^ args[2]
        elseif length(args) == 1
            op(unwrap_const(args[1]))
        elseif length(args) == 2
            op(unwrap_const(args[1]), unwrap_const(args[2]))
        elseif length(args) == 3
            op(unwrap_const(args[1]), unwrap_const(args[2]), unwrap_const(args[3]))
        else
            op(unwrap_const.(args)...)
        end
    else
        maketerm(T, op, args, meta)
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

"""
    occursin(needle::Symbolic, haystack::Symbolic)

Determine whether the second argument contains the first argument. Note that
this function doesn't handle associativity, commutativity, or distributivity.
"""
Base.occursin(needle::Symbolic, haystack::Symbolic) = _occursin(needle, haystack)
Base.occursin(needle, haystack::Symbolic) = _occursin(needle, haystack)
Base.occursin(needle::Symbolic, haystack) = _occursin(needle, haystack)
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
