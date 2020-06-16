##### Numeric simplification

"""
simplify(x; rewriter=default_simplifier(),
            threaded=false,
            polynorm=true,
            thread_subtree_cutoff=100)

Simplify an expression (`x`) by applying `rewriter` until there are no changes.
`polynorm=true` applies `polynormalize` in the beginning of each fixpoint iteration.
"""
function simplify(x;
                  polynorm=false,
                  threaded=false,
                  thread_subtree_cutoff=100,
                  rewriter=nothing)
    if rewriter === nothing
        if threaded
            threaded_simplifier(thread_subtree_cutoff)(to_symbolic(x))
        elseif polynorm
            serial_polynormal_simplifier(to_symbolic(x))
        else
            serial_simplifier(to_symbolic(x))
        end
    else
        Fixpoint(rewriter)(to_symbolic(x))
    end
end

Base.@deprecate simplify(x, ctx; kwargs...)  simplify(x; rewriter=ctx, kwargs...)

"""
    substitute(expr, dict)

substitute any subexpression that matches a key in `dict` with
the corresponding value.
"""
function substitute(expr, dict; fold=true)
    rs = Prewalk(PassThrough(@rule ~x::(x->haskey(dict, x)) => dict[~x]))
    if fold
        rs(expr) |> SymbolicUtils.fold
    else
        rs(expr)
    end
end
