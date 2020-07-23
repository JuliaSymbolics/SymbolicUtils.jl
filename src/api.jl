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
    f = if rewriter === nothing
        if threaded
            threaded_simplifier(thread_subtree_cutoff)
        elseif polynorm
            serial_polynormal_simplifier
        else
            serial_simplifier
        end
    else
        Fixpoint(rewriter)
    end

    PassThrough(f)(x)
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
