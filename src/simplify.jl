
"""
```julia
simplify(x; expand=false,
            threaded=false,
            thread_subtree_cutoff=100,
            rewriter=nothing)
```

Simplify an expression (`x`) by applying `rewriter` until there are no changes.
`expand=true` applies [`expand`](/api/#expand) in the beginning of each fixpoint iteration.

By default, simplify will assume denominators are not zero and allow cancellation in fractions.
Pass `simplify_fractions=false` to prevent this.
"""
function simplify(x;
                  expand=false,
                  polynorm=nothing,
                  threaded=false,
                  simplify_fractions=true,
                  thread_subtree_cutoff=100,
                  rewriter=nothing)
    if polynorm !== nothing
        Base.depwarn("simplify(..; polynorm=$polynorm) is deprecated, use simplify(..; expand=$polynorm) instead",
                        :simplify)
    end


    f = if rewriter === nothing
        if threaded
            threaded_simplifier(thread_subtree_cutoff)
        elseif expand
            serial_expand_simplifier
        else
            serial_simplifier
        end
    else
        Fixpoint(rewriter)
    end

    x = PassThrough(f)(x)
    simplify_fractions && has_operation(x, /) ?
        SymbolicUtils.simplify_fractions(x) : x
end

has_operation(x, op) = (istree(x) && (operation(x) == op ||
                                      any(a->has_operation(a, op),
                                          unsorted_arguments(x))))

Base.@deprecate simplify(x, ctx; kwargs...)  simplify(x; rewriter=ctx, kwargs...)
