
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
function substitute(expr, dict; fold=true, similarterm=similarterm)
    haskey(dict, expr) && return dict[expr]

    if istree(expr)
        op = substitute(operation(expr), dict; fold=fold)
        if fold
            canfold = !(op isa Symbolic)
            args = map(unsorted_arguments(expr)) do x
                x′ = substitute(x, dict; fold=fold)
                canfold = canfold && !(x′ isa Symbolic)
                x′
            end
            canfold && return op(args...)
            args
        else
            args = map(x->substitute(x, dict, fold=fold), unsorted_arguments(expr))
        end

        similarterm(expr,
                    op,
                    args,
                    symtype(expr);
                    metadata=metadata(expr))
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

    if istree(haystack)
        args = arguments(haystack)
        for arg in args
            occursin(needle, arg) && return true
        end
    end
    return false
end
