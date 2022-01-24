function _substitute(expr, dict; fold)
    haskey(dict, expr) && return dict[expr]
    istree(expr) || return expr    

    op = substitute(operation(expr), dict; fold=fold)
    if fold
        canfold = !(op isa Symbolic)
        args = map(unsorted_arguments(expr)) do x
            x′ = substitute(x, dict; fold=fold)
            canfold = canfold && !(x′ isa Symbolic)
            x′
        end
        canfold && return op(args...)
    else
        args = map(x->substitute(x, dict, fold=fold), unsorted_arguments(expr))
    end

    similarterm(expr,
                op,
                args,
                symtype(expr);
                metadata=metadata(expr))
end

"""
    substitute(expr, dict)

substitute any subexpression that matches a key in `dict` with
the corresponding value. 

```julia
julia> substitute(1+sqrt(y), Dict(y => 2))
1 + sqrt(2)
```
"""
substitute(expr, dict) = _substitute(expr, dict; fold=false)

"""
    evaluate(expr, dict)

Evaluate the expression, substituting any subexpression that matches a key in `dict` 
with the corresponding value. 

```julia
julia> evaluate(1+sqrt(y), Dict(y => 2))
2.414213562373095
"""
evaluate(expr, dict) = _substitute(expr, dict, fold=true)


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
