_normalize_integral_rationals(x::Rational) = denominator(x) == 1 ? numerator(x) : x
_normalize_integral_rationals(x) = x

function _normalize_integral_rationals(x::BasicSymbolic{T}) where {T}
    if !iscall(x)
        value = unwrap_const(x)
        if value isa Rational && denominator(value) == 1
            return Const{T}(numerator(value))
        end
        return x
    end
    args = arguments(x)
    normalized_args = map(_normalize_integral_rationals, args)
    any(i -> normalized_args[i] !== args[i], eachindex(args)) || return x
    rebuilt = if isterm(x)
        ConstructionBase.setproperties(x, (; args = ArgsT{T}(normalized_args)))
    else
        maketerm(typeof(x), operation(x), normalized_args, metadata(x); type = symtype(x))
    end
    return rebuilt::BasicSymbolic{T}
end

"""
```julia
simplify(x; expand=false,
            threaded=false,
            thread_subtree_cutoff=100,
            rewriter=nothing)
```

Simplify an expression (`x`) by applying `rewriter` until there are no changes.
Integral rational constants are normalized to integers before rewriting.
`expand=true` applies [`expand`](@ref) in the beginning of each fixpoint iteration.

By default, simplify will assume denominators are not zero and allow cancellation in fractions.
Pass `simplify_fractions=false` to prevent this.
"""
@inline function simplify(
        x;
        expand = false,
        polynorm = nothing,
        threaded = false,
        simplify_fractions = true,
        thread_subtree_cutoff = 100,
        rewriter = nothing
    )
    if polynorm !== nothing
        Base.depwarn(
            "simplify(..; polynorm=$polynorm) is deprecated, use simplify(..; expand=$polynorm) instead",
            :simplify
        )
        expand = polynorm  # Use polynorm value as expand for backward compatibility
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

    x = _normalize_integral_rationals(x)
    x = PassThrough(f)(x)
    return simplify_fractions && query(isdiv, x) ?
        SymbolicUtils.simplify_fractions(x) : x
end

Base.@deprecate simplify(x, ctx; kwargs...)  simplify(x; rewriter = ctx, kwargs...)
