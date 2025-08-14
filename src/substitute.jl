struct Substituter{D <: AbstractDict}
    dict::D
end

function (s::Substituter)(expr)
    haskey(s.dict, expr) ? s.dict[expr] : expr
end

function combine_fold(::Type{T}, op, args, meta) where {T}
    can_fold = !(op isa Symbolic) && all(x -> !(x isa Symbolic) && !Code._is_tuple_or_array_of_symbolics(x), args)
    can_fold ? op(args...) : maketerm(T, op, args, meta)
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
    isequal(needle, haystack) && return true
    if iscall(haystack)
        args = arguments(haystack)
        for arg in args
            if needle isa Integer || needle isa AbstractFloat
                isequal(needle, arg) && return true
            else
               occursin(needle, arg) && return true
            end
        end
    end
    return false
end
