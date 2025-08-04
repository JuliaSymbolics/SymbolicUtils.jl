# A total ordering

<ₑ(a::Real,    b::Real) = abs(a) < abs(b)
<ₑ(a::Complex, b::Complex) = (abs(real(a)), abs(imag(a))) < (abs(real(b)), abs(imag(b)))
<ₑ(a::Real,    b::Complex) = true
<ₑ(a::Complex, b::Real) = false

<ₑ(a::Symbolic, b::Number) = false
<ₑ(a::Number,   b::Symbolic) = true

<ₑ(a::Function, b::Function) = nameof(a) <ₑ nameof(b)

<ₑ(a::Type, b::Type) = nameof(a) <ₑ nameof(b)
<ₑ(a::T, b::S) where{T,S} = T<S
<ₑ(a::T, b::T) where{T} = a < b

"""
$(SIGNATURES)

Get the degrees of symbols within a given expression.

This internal function is used to define the order of terms in a symbolic expression,
which is a variation on degree lexicographic order. It is used for printing and
by [`sorted_arguments`](@ref).

Returns a tuple of degree and lexicographically sorted *multiplier* ⇒ *power* pairs,
where the *multiplier* is a tuple of the symbol optionally followed by its indices.
For a sum expression, returns the `get_degrees()` result for term with the highest degree.

See also `monomial_lt` and `lexlt`.
"""
function get_degrees(expr)
    degs_cache = Dict()
    res = _get_degrees(expr, degs_cache)
    if res isa AbstractVector
        return Tuple(res)
    else
        return res
    end
end

function _get_degrees(expr, degs_cache::AbstractDict)
    if issym(expr)
        return get!(() -> ((Symbol(expr),) => 1,), degs_cache, expr)
    elseif iscall(expr)
        # operation-specific degree handling
        return _get_degrees(operation(expr), expr, degs_cache)
    else
        return () # skip numbers and unsupported expressions
    end
end

# fallback for unsupported operation
_get_degrees(::Any, expr, degs_cache) =
    ((Symbol("zzzzzzz", hash(expr)),) => 1,)

_getindex_symbol(arr, i) = Symbol(arr[i])

function _get_degrees(::typeof(getindex), expr, degs_cache)
    args = arguments(expr)
    @inbounds return get!(() -> (ntuple(Base.Fix1(_getindex_symbol, args), length(args)) => 1,),
                degs_cache, expr)
end

function _get_degrees(::typeof(*), expr, degs_cache)
    args = arguments(expr)
    ds = sizehint!(Vector{Any}(), length(args))
    for arg in args
        degs = _get_degrees(arg, degs_cache)
        append!(ds, degs)
    end
    return sort!(ds)
end

function _get_degrees(::typeof(+), expr, degs_cache)
    # among the terms find the best in terms of monomial_lt
    sel_degs = ()
    sel_degsum = 0
    for arg in arguments(expr)
        degs = _get_degrees(arg, degs_cache)
        degsum = sum(last, degs, init=0)
        if (sel_degs == ()) || (degsum > sel_degsum) ||
           (degsum == sel_degsum && lexlt(degs, sel_degs))
            sel_degs, sel_degsum = degs, degsum
        end
    end
    return sel_degs
end

function _get_degrees(::typeof(^), expr, degs_cache)
    base_expr, pow_expr = arguments(expr)
    if pow_expr isa Real
        @inbounds degs = map(_get_degrees(base_expr, degs_cache)) do (base, pow)
            (base => pow * pow_expr)
        end
        if pow_expr < 0 && length(degs) > 1
            # fix the order after the powers were negated
            isa(degs, AbstractVector) || (degs = collect(degs))
            sort!(degs)
        end
        return degs
    else
        # expression in the power argument is not supported
        return _get_degrees(nothing, expr, degs_cache)
    end
end

function _get_degrees(::typeof(/), expr, degs_cache)
    nom_expr, denom_expr = arguments(expr)
    if denom_expr isa Number # constant denominator
        return _get_degrees(nom_expr, degs_cache)
    elseif nom_expr isa Number # constant nominator
        @inbounds degs = map(_get_degrees(denom_expr, degs_cache)) do (base, pow)
            (base => -pow)
        end
        isa(degs, AbstractVector) || (degs = collect(degs))
        return sort!(degs)
    else
        # TODO expressions in both nom and denom are not yet supported
        return _get_degrees(nothing, expr, degs_cache)
    end
end

function monomial_lt(degs1, degs2)
    d1 = sum(last, degs1, init=0)
    d2 = sum(last, degs2, init=0)
    d1 != d2 ?
        # lower absolute degree first, or if equal, positive degree first
        (abs(d1) < abs(d2) || abs(d1) == abs(d2) && d1 > d2) :
        lexlt(degs1, degs2)
end

function lexlt(degs1, degs2)
    for ((a_base, a_deg), (b_base, b_deg)) in zip(degs1, degs2)
        if a_base == b_base && a_deg != b_deg
            # same base, higher absolute degree first, positive degree first
            return abs(a_deg) > abs(b_deg) || abs(a_deg) == abs(b_deg) && a_deg > b_deg
        elseif a_base != b_base
            # lexicographic order for the base
            return a_base < b_base
        end
    end
    return false # they are equal
end

_arglen(a) = iscall(a) ? length(arguments(a)) : 0

function <ₑ(a::Tuple, b::Tuple)
    for (x, y) in zip(a, b)
        if x <ₑ y
            return true
        elseif y <ₑ x
            return false
        end
    end
    return length(a) < length(b)
end

function <ₑ(a::BasicSymbolic, b::BasicSymbolic)
    da, db = get_degrees(a), get_degrees(b)
    fw = monomial_lt(da, db)
    bw = monomial_lt(db, da)
    if fw === bw && !isequal(a, b)
        if _arglen(a) == _arglen(b)
            return (operation(a), arguments(a)...,) <ₑ (operation(b), arguments(b)...,)
        else
            return _arglen(a) < _arglen(b)
        end
    else
        return fw
    end
end
