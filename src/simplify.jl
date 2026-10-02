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
            trig_reduce=false,
            thread_subtree_cutoff=100,
            rewriter=nothing)
```

Simplify an expression (`x`) by applying `rewriter` until there are no changes.
Integral rational constants are normalized to integers before rewriting.
`expand=true` applies [`expand`](@ref) in the beginning of each fixpoint iteration.

`trig_reduce` converts trigonometric powers and products to sums of linear
harmonics (product-to-sum identities and power reduction), analogous to
Mathematica's `TrigReduce`. Accepts:
- `false` (default): no trig reduction
- `true`: reduce all trig functions
- a variable or vector of variables: only reduce trig functions involving those variables

See also [`trig_reduce`](@ref) for a standalone convenience function.

By default, simplify will assume denominators are not zero and allow cancellation in fractions.
Pass `simplify_fractions=false` to prevent this.
"""
@inline function simplify(x;
                  expand=false,
                  polynorm=nothing,
                  threaded=false,
                  trig_reduce=false,
                  simplify_fractions=true,
                  thread_subtree_cutoff=100,
                  rewriter=nothing)
    if polynorm !== nothing
        Base.depwarn("simplify(..; polynorm=$polynorm) is deprecated, use simplify(..; expand=$polynorm) instead",
                        :simplify)
        expand = polynorm  # Use polynorm value as expand for backward compatibility
    end

    # trig_reduce accepts: false, true, or a vector of target variables
    _trig_reduce_active = trig_reduce !== false
    _trig_reduce_vars = if trig_reduce isa AbstractVector
        trig_reduce
    elseif trig_reduce isa BasicSymbolic
        [trig_reduce]
    else
        nothing
    end

    # If vars are specified, delegate to the standalone trig_reduce function
    # which handles variable targeting with bounded iteration
    if _trig_reduce_active && _trig_reduce_vars !== nothing
        x = SymbolicUtils.trig_reduce(x; vars=_trig_reduce_vars)
        return simplify_fractions && query(isdiv, x) ?
            SymbolicUtils.simplify_fractions(x) : x
    end

    f = if rewriter === nothing
        if threaded
            threaded_simplifier(thread_subtree_cutoff; trig_reduce=_trig_reduce_active)
        elseif _trig_reduce_active
            serial_trig_reduce_simplifier
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
    simplify_fractions && query(isdiv, x) ?
        SymbolicUtils.simplify_fractions(x) : x
end

"""
    trig_reduce(x; vars=nothing, maxiters=50)

Reduce trigonometric and hyperbolic powers and products to sums of linear harmonics.

Applies product-to-sum identities for circular and hyperbolic functions:

    cos(A)cos(B)   → [cos(A-B) + cos(A+B)] / 2
    sin(A)sin(B)   → [cos(A-B) - cos(A+B)] / 2
    sin(A)cos(B)   → [sin(A+B) + sin(A-B)] / 2
    cosh(A)cosh(B) → [cosh(A-B) + cosh(A+B)] / 2
    sinh(A)sinh(B) → [cosh(A+B) - cosh(A-B)] / 2
    sinh(A)cosh(B) → [sinh(A+B) + sinh(A-B)] / 2

Power-reduction identities for arbitrary integer powers n ≥ 2:

    cos(x)^n, sin(x)^n   → multi-angle expansion
    cosh(x)^n, sinh(x)^n → multi-angle expansion
    tan(x)^2  → sec(x)^2 - 1
    cot(x)^2  → csc(x)^2 - 1

Exponential rules (exp(x)*exp(y) → exp(x+y)) are also included.

## Arguments
- `vars`: If provided, only reduce trig functions whose arguments involve the
  specified variables.  Pass a single symbol or a vector of symbols.
  Default `nothing` reduces all trig functions.
- `maxiters`: Maximum number of expand-reduce iterations (default 50).
  The loop terminates early if a fixed point is reached.

## Examples
```julia
@syms x y r θ
trig_reduce(cos(x)^2)                     # → 1/2 + cos(2x)/2
trig_reduce(cos(x) * cos(3x))             # → cos(2x)/2 + cos(4x)/2
trig_reduce(cos(x)^3)                     # → 3cos(x)/4 + cos(3x)/4
trig_reduce(r^3 * cos(θ)^3; vars=[θ])     # reduces cos(θ)^3 but keeps r^3 untouched
trig_reduce(cos(x)*cos(y); vars=[x])      # only reduces if argument involves x
```

See also: [`simplify`](@ref), [`expand`](@ref).
"""
function trig_reduce(x; vars=nothing, maxiters::Int=50)
    rw = if vars === nothing
        get_default_simplifier(trig_reduce=true)
    else
        target = vars isa AbstractVector ? vars : [vars]
        get_default_simplifier(trig_reduce=true, trig_reduce_vars=target)
    end
    current = x
    for _ in 1:maxiters
        !iscall(current) && break
        expanded = expand(current)
        reduced = PassThrough(If(iscall, rw))(expanded)
        if isequal(reduced, current)
            return reduced
        end
        current = reduced
    end
    return current
end

Base.@deprecate simplify(x, ctx; kwargs...)  simplify(x; rewriter=ctx, kwargs...)
