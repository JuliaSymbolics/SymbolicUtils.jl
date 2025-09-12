
"""
```julia
simplify(x; expand=false,
            threaded=false,
            thread_subtree_cutoff=100,
            trigexpand=true,
            rewriter=nothing)
```

Simplify an expression (`x`) by applying `rewriter` until there are no changes.
`expand=true` applies [`expand`](/api/#expand) in the beginning of each fixpoint iteration.
`trigexpand=true` (default) applies trigonometric product-to-sum identities such as `cos(A)*cos(B) = (cos(A-B) + cos(A+B))/2`.
Pass `trigexpand=false` to disable trigonometric product-to-sum transformations.

By default, simplify will assume denominators are not zero and allow cancellation in fractions.
Pass `simplify_fractions=false` to prevent this.
"""
function simplify(x;
                  expand=false,
                  polynorm=nothing,
                  threaded=false,
                  simplify_fractions=true,
                  trigexpand=true,
                  thread_subtree_cutoff=100,
                  rewriter=nothing)
    if polynorm !== nothing
        Base.depwarn("simplify(..; polynorm=$polynorm) is deprecated, use simplify(..; expand=$polynorm) instead",
                        :simplify)
        expand = polynorm  # Use polynorm value as expand for backward compatibility
    end

    f = if rewriter === nothing
        if threaded
            Fixpoint(default_simplifier(trigexpand=trigexpand, threaded=true, thread_cutoff=thread_subtree_cutoff))
        elseif expand
            # For expand mode, we need to create a custom simplifier with trigexpand setting
            If(iscall, Fixpoint(Chain((expand, Fixpoint(default_simplifier(trigexpand=trigexpand))))))
        elseif !trigexpand
            # For trigexpand=false (non-default), create custom simplifier
            If(iscall, Fixpoint(default_simplifier(trigexpand=false)))
        else
            # Default case: trigexpand=true (use pre-compiled simplifier)
            serial_simplifier
        end
    else
        Fixpoint(rewriter)
    end

    x = PassThrough(f)(x)
    simplify_fractions && has_operation(x, /) ?
        SymbolicUtils.simplify_fractions(x) : x
end

has_operation(x, op) = (iscall(x) && (operation(x) == op ||
                                      any(a->has_operation(a, op),
                                        arguments(x))))

Base.@deprecate simplify(x, ctx; kwargs...)  simplify(x; rewriter=ctx, kwargs...)
