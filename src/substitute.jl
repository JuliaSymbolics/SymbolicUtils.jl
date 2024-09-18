
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
function substitute(expr, dict; fold=true)
    haskey(dict, expr) && return dict[expr]

    if iscall(expr)
        op = substitute(operation(expr), dict; fold=fold)
        if fold
            canfold = !(op isa Symbolic)
            args = map(arguments(expr)) do x
                x′ = substitute(x, dict; fold=fold)
                if isconst(x)
                    x′ = x′.impl.val
                end
                canfold = canfold && !(x′ isa Symbolic)
                x′
            end
            canfold && return op(args...)
            args
        else
            args = map(x->substitute(x, dict, fold=fold), arguments(expr))
        end

        maketerm(typeof(expr),
                 op,
                 args,
                 metadata(expr))
    else
        expr
    end
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
