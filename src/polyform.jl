export simplify_fractions, quick_cancel, flatten_fractions

"""
    $TYPEDSIGNATURES

Convert a `BasicSymbolic` expression to a polynomial variable, caching the result.

# Arguments
- `bs_to_poly::AbstractDict`: Dictionary cache mapping `BasicSymbolic` to `PolyVarT`
- `x::BasicSymbolic`: The symbolic expression to convert

# Returns
- A `PolyVarT` polynomial variable representing `x`, created or retrieved from cache
"""
function basicsymbolic_to_polyvar(bs_to_poly::AbstractDict, x::BasicSymbolic)::PolyVarT
    get!(bs_to_poly, x) do
        inner_name = _name_as_operator(x)
        name = Symbol(inner_name, :_, hash(x))
        MP.similar_variable(ExamplePolyVar, name)
    end
end

"""
    $TYPEDSIGNATURES

Convert polynomial terms back into `BasicSymbolic` expressions by substitution.

# Arguments
- `poly`: A polynomial expression, either `PolyVarT` or `PolynomialT`
- `vars`: Vector of `BasicSymbolic` variables corresponding to each entry of
  `MultivariatePolynomials.variables(poly)`.

# Returns
- A `BasicSymbolic{T}` expression representing the polynomial with substituted variables
"""
function subs_poly(poly, vars::AbstractVector{BasicSymbolic{T}}) where {T}
    add_buffer = ArgsT{T}()
    mul_buffer = ArgsT{T}()
    for term in MP.terms(poly)
        empty!(mul_buffer)
        coeff = MP.coefficient(term)
        push!(mul_buffer, Const{T}(coeff))
        mono = MP.monomial(term)
        for (i, exp) in enumerate(MP.exponents(mono))
            iszero(exp) && continue
            push!(mul_buffer, (vars[i] ^ exp))
        end
        push!(add_buffer, mul_worker(T, mul_buffer))
    end
    return add_worker(T, add_buffer)
end
function subs_poly(poly::PolyVarT, vars::AbstractVector{BasicSymbolic{T}}) where {T}
    return only(vars)
end

"""
    to_poly!(poly_to_bs, bs_to_poly, expr, recurse = true)

Convert a `BasicSymbolic` expression into a sparse polynomial representation.
`poly_to_bs` maps generated polynomial variables back to symbolic expressions,
while `bs_to_poly` caches the reverse mapping. With `recurse = false`,
non-polynomial subexpressions become single polynomial variables.

# Returns

A [`PolyVarT`](@ref) or [`PolynomialT`](@ref) representing `expr`.
"""
function to_poly!(poly_to_bs::AbstractDict, bs_to_poly::AbstractDict, expr, recurse::Bool = true)
    return _to_poly!(poly_to_bs, bs_to_poly, expr, recurse, false)
end

# `Rational{Int}` arithmetic inside polynomial operations is checked and throws
# `OverflowError`, e.g. when squaring a coefficient with a large denominator.
# With `widen = true` every exact coefficient enters the polynomial as a
# `BigInt`-based number so the same computation can be retried without overflow.
_widen_coeff(x::Integer) = big(x)
_widen_coeff(x::Rational) = Rational{BigInt}(x)
_widen_coeff(x::Complex{<:Union{Integer, Rational}}) = complex(_widen_coeff(real(x)), _widen_coeff(imag(x)))
_widen_coeff(x) = x
_maybe_widen(x, widen::Bool) = widen ? _widen_coeff(x) : x

_narrow_coeff(x::Union{Integer, Rational}) = _narrow(x)
_narrow_coeff(x::Complex{<:Union{Integer, Rational}}) = complex(_narrow(real(x)), _narrow(imag(x)))
_narrow_coeff(x) = x
_narrow_coeffs(p::DP.Polynomial) = PolynomialT(PolyCoeffT[_narrow_coeff(c) for c in MP.coefficients(p)], MP.monomials(p))
_narrow_coeffs(p) = p

function _retry_widened(f)
    try
        return f(false)
    catch e
        e isa OverflowError || rethrow()
        return f(true)
    end
end

_to_poly!(::AbstractDict, ::AbstractDict, expr, ::Bool, widen::Bool) = MA.operate!(+, zeropoly(), _maybe_widen(expr, widen))
function _to_poly!(poly_to_bs::AbstractDict, bs_to_poly::AbstractDict, expr::BasicSymbolic{T}, recurse::Bool, widen::Bool)::Union{PolyVarT, PolynomialT} where {T}
    @match expr begin
        BSImpl.Const(; val) => _to_poly!(poly_to_bs, bs_to_poly, val, recurse, widen)
        BSImpl.Sym(;) => begin
            pvar = basicsymbolic_to_polyvar(bs_to_poly, expr)
            get!(poly_to_bs, pvar, expr)
            return pvar
        end
        BSImpl.AddMul(; coeff, dict, variant) => begin
            @match variant begin
                AddMulVariant.ADD => begin
                    poly = zeropoly()
                    MA.operate!(+, poly, _maybe_widen(MA.copy_if_mutable(coeff), widen))
                    for (k, v) in dict
                        tpoly = _to_poly!(poly_to_bs, bs_to_poly, k, recurse, widen)
                        cv = _maybe_widen(v, widen)
                        if tpoly isa PolyVarT
                            tpoly = tpoly * cv
                        else
                            MA.operate!(*, tpoly, cv)
                        end
                        MA.operate!(+, poly, tpoly)
                    end
                    return poly
                end
                AddMulVariant.MUL => begin
                    poly = onepoly()
                    MA.operate!(*, poly, _maybe_widen(MA.copy_if_mutable(coeff), widen))
                    for (k, v) in dict
                        if safe_isinteger(v)
                            tpoly = _to_poly!(poly_to_bs, bs_to_poly, k, recurse, widen) ^ Int(v)
                        else
                            tpoly = _to_poly!(poly_to_bs, bs_to_poly, k ^ v, recurse, widen)
                        end
                        MA.operate!(*, poly, tpoly)
                    end
                    return poly
                end
            end
        end
        BSImpl.Term(; f, args, type, shape) => begin
            if f === (^) && isconst(args[2]) && (exp = unwrap_const(args[2]); exp isa Real) && safe_isinteger(exp)
                base = args[1]
                poly = _to_poly!(poly_to_bs, bs_to_poly, base, true, widen)
                if poly isa PolyVarT
                    _isone(exp) && return poly
                    mv = DP.MonomialVector{PolyVarOrder, MonomialOrder}([poly], [Int[exp]])
                    return PolynomialT(PolyCoeffT[1], mv)
                end
                poly = poly ^ Int(exp)
                new_expr = from_poly(poly_to_bs, poly)
                if !isequal(expr, new_expr)
                    poly = _to_poly!(poly_to_bs, bs_to_poly, from_poly(poly_to_bs, poly), recurse, widen)
                end
                return poly
            elseif f === (*) || f === (+)
               arg1, restargs = Iterators.peel(args)
                poly = _to_poly!(poly_to_bs, bs_to_poly, arg1, true, widen)
                if !(poly isa PolynomialT)
                    _poly = zeropoly()
                    MA.operate!(+, _poly, poly)
                    poly = _poly
                end
                for arg in restargs
                    MA.operate!(f, poly, _to_poly!(poly_to_bs, bs_to_poly, arg, true, widen))
                end
                return poly
            else
                if recurse
                    expr = BSImpl.Term{T}(f, map(expand, args); type, shape)
                end
                pvar = basicsymbolic_to_polyvar(bs_to_poly, expr)
                get!(poly_to_bs, pvar, expr)
                return pvar
            end
        end
        BSImpl.Div(; num, den, type, shape) => begin
            if isconst(den)
                npoly = _to_poly!(poly_to_bs, bs_to_poly, num, recurse, widen)
                den = _maybe_widen(unwrap_const(den), widen)
                if npoly isa PolyVarT
                    mv = DP.MonomialVector{PolyVarOrder, MonomialOrder}([npoly], [Int[1]])
                    coeff = den isa Union{Integer, Rational} ? (1 // den) : (1 / den)
                    return PolynomialT(PolyCoeffT[coeff], mv)
                elseif den isa Union{Integer, Rational}
                    coeffs = MP.coefficients(npoly)
                    for (i, c) in enumerate(coeffs)
                        coeffs[i] = c isa Union{Integer, Rational} ? (c // den) : (c / den)
                    end
                    return npoly
                else
                    coeffs = MP.coefficients(npoly)
                    map!(Base.Fix2(/, den), coeffs, coeffs)
                    return npoly
                end
            end
            if recurse
                expr = BSImpl.Div{T}(expand(num), expand(den), false; type, shape)
            end
            pvar = basicsymbolic_to_polyvar(bs_to_poly, expr)
            get!(poly_to_bs, pvar, expr)
            return pvar
        end
        _ => begin
            # `ArrayOp` and `ArrayMaker` are not polynomial in their scalar entries;
            # treat them as opaque variables like any other non-algebraic term.
            pvar = basicsymbolic_to_polyvar(bs_to_poly, expr)
            get!(poly_to_bs, pvar, expr)
            return pvar
        end
    end
end

"""
    from_poly(poly_to_bs, poly)

Reconstruct a `BasicSymbolic` expression from a polynomial produced by
[`to_poly!`](@ref). `poly_to_bs` must contain an entry for every polynomial
variable in `poly`.

# Returns

A `BasicSymbolic` expression with the same polynomial value.
"""
function from_poly(poly_to_bs::AbstractDict{PolyVarT, BasicSymbolic{T}}, poly) where {T}
    partial_pvars = MP.variables(poly)
    vars = SmallV{BasicSymbolic{T}}()
    sizehint!(vars, length(partial_pvars))
    for ppvar in partial_pvars
        var = poly_to_bs[ppvar]
        push!(vars, var)
    end
    return subs_poly(poly, vars)::BasicSymbolic{T}
end

"""
    expand(expr)

Expand expressions by distributing multiplication over addition, e.g.,
`a*(b+c)` becomes `ab+ac`.

`expand` uses replace symbols and non-algebraic expressions by variables of type
`variable_type` to compute the distribution using a specialized sparse
multivariate polynomials implementation.
`variable_type` can be any subtype of `MultivariatePolynomials.AbstractVariable`.
"""
function expand(expr::BasicSymbolic{T}, recurse = true)::BasicSymbolic{T} where {T}
    iscall(expr) || return expr
    return _retry_widened() do widen
        poly_to_bs = Dict{PolyVarT, BasicSymbolic{T}}()
        bs_to_poly = Dict{BasicSymbolic{T}, PolyVarT}()
        partial_poly = _to_poly!(poly_to_bs, bs_to_poly, expr, recurse, widen)
        from_poly(poly_to_bs, widen ? _narrow_coeffs(partial_poly) : partial_poly)
    end
end
expand(x, _...) = x

## Rational Polynomial form with Div

function simplify_div(d::T)::T where {T <: BasicSymbolic}
    isdiv(d) || return d
    d.simplified && return d
    num, den = simplify_div(d.num, d.den)
    isequal(num, d) && return d
    return simplify_fractions(num) / simplify_fractions(den)
end

function canonicalize_coeffs!(coeffs::Vector{PolyCoeffT})
    for i in eachindex(coeffs)
        v = coeffs[i]
        safe_isinteger(v) || continue
        # Int64: on 32-bit Julia, `Int` is Int32 and overflows in MP.gcd/content.
        coeffs[i] = Int64(v)
    end
end
canonicalize_coeffs!(x) = nothing

function poly_to_gcd_form(p::PolynomialT)
    all_int = true
    all_rat = true
    any_complex = false
    for c in MP.coefficients(p)
        isint = safe_isinteger(c)
        all_int &= isint
        all_rat &= isint || c isa Rational
        any_complex |= c isa Complex
        all_int || all_rat || break
    end
    # Always widen integer/rational coefficients to Int64 / Rational{Int64}.
    # On 32-bit Julia, `Int` is Int32; homogeneous `Integer.(::Vector{Int32})`
    # stays Int32 and then `MP.gcd` / `div_multiple` hits DivideError when
    # content arithmetic overflows (e.g. MomentClosure derivative matching
    # closures going through `simplify` → `simplify_fractions`).
    # `safe_isinteger` bounds integers by `typemax(Int)`, but a `Rational` can be
    # arbitrarily large, so `Rational{Int64}` is only a floor for the rational branch.
    cs = if all_int
        Int64.(MP.coefficients(p))
    elseif all_rat
        rs = map(c -> c isa Rational ? c : rationalize(c), MP.coefficients(p))
        convert(Vector{mapreduce(typeof, promote_type, rs; init = Rational{Int64})}, rs)
    elseif any_complex
        (complex ∘ float).(MP.coefficients(p))
    else
        float.(MP.coefficients(p))
    end
    # Broadcast can still leave an abstract eltype for heterogeneous floats;
    # narrow to a concrete eltype when needed (gcd requires it).
    if !isconcretetype(eltype(cs))
        T = isempty(cs) ? (all_int ? Int64 : all_rat ? Rational{Int64} :
                           any_complex ? ComplexF64 : Float64) :
            mapreduce(typeof, promote_type, cs)
        cs = Vector{T}(cs)
    end
    return DP.Polynomial(cs, MP.monomials(p))
end

function safe_gcd(p1::Union{PolyVarT, PolynomialT}, p2::Union{PolyVarT, PolynomialT})
    if p1 isa PolyVarT && p2 isa PolyVarT
        return gcd(p1, p2)
    elseif p1 isa PolyVarT && p2 isa PolynomialT
        return gcd(p1, poly_to_gcd_form(p2))
    elseif p1 isa PolynomialT && p2 isa PolyVarT
        return gcd(poly_to_gcd_form(p1), p2)
    elseif p1 isa PolynomialT && p2 isa PolynomialT
        return gcd(poly_to_gcd_form(p1), poly_to_gcd_form(p2))
    end
end

function simplify_div(num::BasicSymbolic{T}, den::BasicSymbolic{T}) where {T <: SymVariant}
    return _retry_widened(widen -> _simplify_div(num, den, widen))
end

function _simplify_div(num::BasicSymbolic{T}, den::BasicSymbolic{T}, widen::Bool) where {T <: SymVariant}
    poly_to_bs = Dict{PolyVarT, BasicSymbolic{T}}()
    bs_to_poly = Dict{BasicSymbolic{T}, PolyVarT}()
    partial_poly1 = _to_poly!(poly_to_bs, bs_to_poly, num, false, widen)
    partial_poly2 = _to_poly!(poly_to_bs, bs_to_poly, den, false, widen)
    factor = safe_gcd(partial_poly1, partial_poly2)
    if isone(factor)
        return num, den
    end
    # `factor` was computed on `poly_to_gcd_form` conversions, so the partial
    # polynomials must use matching concrete coefficient types; otherwise
    # `div_multiple` mixes e.g. `Rational{BigInt}` and `Rational{Int64}`
    # coefficients and hits unimplemented MutableArithmetics buffered paths.
    partial_poly1 isa PolynomialT && (partial_poly1 = poly_to_gcd_form(partial_poly1))
    partial_poly2 isa PolynomialT && (partial_poly2 = poly_to_gcd_form(partial_poly2))
    # NOTE: This does not mutate `partial_poly1` to be the result, it just
    # uses it as buffer. The result is the returned value.
    partial_poly1 = MP.div_multiple(partial_poly1, factor, MA.IsMutable())
    partial_poly2 = MP.div_multiple(partial_poly2, factor, MA.IsMutable())
    canonicalize_coeffs!(MP.coefficients(partial_poly1))
    canonicalize_coeffs!(MP.coefficients(partial_poly2))
    if widen
        partial_poly1 = _narrow_coeffs(partial_poly1)
        partial_poly2 = _narrow_coeffs(partial_poly2)
    end
    return from_poly(poly_to_bs, partial_poly1), from_poly(poly_to_bs, partial_poly2)
end

"""
    quick_cancel(d)

Cancel out matching factors from numerator and denominator.
This is not as effective as `simplify_fractions`, for example,
it wouldn't simplify `(x^2 + 15 -  8x)  / (x - 5)` to `(x - 3)`.
But it will simplify `(x - 5)^2*(x - 3) / (x - 5)` to `(x - 5)*(x - 3)`.
Has optimized processes for `Mul` and `Pow` terms.
"""
quick_cancel(d) = d
function quick_cancel(d::BasicSymbolic{T})::BasicSymbolic{T} where {T}
    iscall(d) || return d
    op = operation(d)
    if op === (^)
        base, exp = arguments(d)
        isconst(base) && return d
        isdiv(base) || return d
        num, den = quick_cancel(base.num, base.den)
        return Div{T}(num ^ exp, den ^ exp, false; type = symtype(d))
    elseif op === (/)
        num, den = arguments(d)
        num, den = quick_cancel(num, den)
        return Div{T}(num, den, false; type = symtype(d))
    else
        return d
    end
end

function quick_cancel(x::S, y::S)::Tuple{S, S} where {T <: SymVariant, S <: BasicSymbolic{T}}
    isequal(x, y) && return one_of_vartype(T), one_of_vartype(T)
    opx = iscall(x) ? operation(x) : nothing
    opy = iscall(y) ? operation(y) : nothing
    icx = isconst(x)
    icy = isconst(y)
    if opx === (^) && opy === (^)
        return quick_powpow(x, y)
    elseif opx === (*) && opy === (^)
        return quick_mulpow(x, y)
    elseif opx === (^) && opy === (*)
        return reverse(quick_mulpow(y, x))
    elseif opx === (*) && opy === (*)
        return quick_mulmul(x, y)
    elseif opx === (^) && !icy
        return quick_pow(x, y)
    elseif opy === (^) && !icx
        return reverse(quick_pow(y, x))
    elseif opx === (*) && !icy
        return quick_mul(x, y)
    elseif opy === (*) && !icx
        return reverse(quick_mul(y, x))
    else
        return x, y
    end
end

# ispow(x) case
function quick_pow(x::S, y::S)::Tuple{S, S} where {T <: SymVariant, S <: BasicSymbolic{T}}
    base, exp = arguments(x)
    exp = unwrap_const(exp)
    exp isa Number || return (x, y)
    isequal(base, y) && exp >= 1 ? (base ^ (exp - 1), one_of_vartype(T)) : (x, y)
end

# Double Pow case
function quick_powpow(x::S, y::S)::Tuple{S, S} where {T <: SymVariant, S <: BasicSymbolic{T}}
    base1, exp1 = arguments(x)
    base2, exp2 = arguments(y)
    isequal(base1, base2) || return x, y
    exp1 = unwrap_const(exp1)
    exp2 = unwrap_const(exp2)
    !(exp1 isa Number && exp2 isa Number) && return (x, y)
    if exp1 > exp2
        return base1 ^ (exp1 - exp2), one_of_vartype(T)
    elseif exp1 == exp2
        return one_of_vartype(T), one_of_vartype(T)
    else # exp1 < exp2
        return one_of_vartype(T), base2 ^ (exp2 - exp1)
    end
end

# ismul(x)
function quick_mul(x::S, y::S)::Tuple{S, S} where {T <: SymVariant, S <: BasicSymbolic{T}}
    yy = BSImpl.Term{T}(^, ArgsT{T}((y, one_of_vartype(T))); type = symtype(y))
    newx, newy = quick_mulpow(x, yy)
    return isequal(newy, yy) ? (x, y) : (newx, newy)
end

# mul, pow case
function quick_mulpow(x::S, y::S)::Tuple{S, S} where {T <: SymVariant, S <: BasicSymbolic{T}}
    base, exp = arguments(y)
    exp = unwrap_const(exp)
    exp isa Number || return (x, y)
    args = parent(arguments(x))
    idx = 0
    argbase = argexp = nothing
    @union_split_smallvec args begin
        for (i, arg) in enumerate(args)
            if isequal(arg, base)
                idx = i
                argbase = arg
                argexp = 1
                break
            end

            if iscall(arg) && operation(arg) === (^) && isequal(arguments(arg)[1], base)
                idx = i
                argbase, argexp = arguments(arg)
                break
            end
        end
    end
    iszero(idx) && return x, y
    argexp = unwrap_const(argexp)
    argexp isa Number || return x, y
    # cheat by mutating `args` to avoid allocating
    oldval = args[idx]
    if argexp > exp
        args[idx] = argbase ^ (argexp - exp)
        result = mul_worker(T, args), one_of_vartype(T)
    elseif argexp == exp
        args[idx] = one_of_vartype(T)
        result = mul_worker(T, args), one_of_vartype(T)
    else
        args[idx] = one_of_vartype(T)
        result = mul_worker(T, args), base ^ (exp - argexp)
    end
    args[idx] = oldval
    return result
end

# Double mul case
function quick_mulmul(x::S, y::S)::Tuple{S, S} where {T <: SymVariant, S <: BasicSymbolic{T}}
    @match (x, y) begin
        (BSImpl.AddMul(; coeff = c1, dict = d1, type = t1, shape = s1, variant = vr1), BSImpl.AddMul(; coeff = c2, dict = d2, type = t2, shape = s2, variant = vr2)) => begin
            newd1 = d1
            newd2 = d2
            for (k1, v1) in d1
                haskey(d2, k1) || continue
                v2 = d2[k1]
                if newd1 === d1
                    newd1 = copy(d1)
                    newd2 = copy(d2)
                end
                delete!((v1 >= v2) ? newd2 : newd1, k1)
                setindex!((v1 >= v2) ? newd1 : newd2, abs(v1 - v2), k1)
            end
            if newd1 === d1
                return x, y
            end
            filter!(!iszero ∘ last, newd1)
            filter!(!iszero ∘ last, newd2)
            xx = Mul{T}(c1, newd1; type = t1, shape = s1)
            yy = Mul{T}(c2, newd2; type = t2, shape = s2)

            return xx, yy
        end
        # Not `_unreachable` since `adjoint(vec) * vec` can end up here, and we just want
        # to ignore it.
        _ => (x, y)
    end
end

function add_with_div(x::BasicSymbolic{T})::BasicSymbolic{T} where {T}
    (!iscall(x) || operation(x) !== (+)) && return x
    aa = parent(arguments(x))
    !any(isdiv, aa) && return x # no rewrite necessary

    # find and multiply all denominators
    dens = ArgsT{T}()
    for a in aa
        isdiv(a) || continue
        push!(dens, a.den)
    end
    type = symtype(x)
    den = mul_worker(T, dens)

    # add all numerators
    div_idx = 1
    nums = ArgsT{T}()
    for a in aa
        # if it is a division, we don't want to multiply the numerator by
        # its own denominator, so temporarily overwrite the index in `dens`
        # that is the denominator of this term (tracked by `div_idx`), multiply
        # and voila! numerator. Remember to reset `dens` at the end.
        if isdiv(a)
            _den = dens[div_idx]
            dens[div_idx] = a.num
            _num = mul_worker(T, dens)
            dens[div_idx] = _den
            div_idx += 1
        else
            _num = den * a
        end
        push!(nums, _num)
    end
    num = add_worker(T, nums)

    num, den = quick_cancel(num, den)
    return num / den
end

const FRAC_SIMPLIFIER = Rewriters.Postwalk(simplify_div ∘ quick_cancel) ∘ Rewriters.Postwalk(add_with_div)
const QUICK_CANCELER = Rewriters.Postwalk(quick_cancel)

"""
    simplify_fractions(x; polyform=false)

Find `Div` nodes and simplify them by cancelling a set of factors of numerators
and denominators.
"""
function simplify_fractions(x::BasicSymbolic{T})::BasicSymbolic{T} where {T}

    x = QUICK_CANCELER(x)

    !needs_div_rules(x) && return x

    return FRAC_SIMPLIFIER(x)
end
simplify_fractions(x) = x

const FRACTION_FLATTENER = Rewriters.Fixpoint(Rewriters.Postwalk(add_with_div))

"""
    flatten_fractions(x)

Flatten nested fractions that are added together.

```julia-repl
julia> flatten_fractions((1+(1+1/a)/a)/a)
(1 + a + a^2) / (a^3)
```
"""
function flatten_fractions(x::BasicSymbolic{T})::BasicSymbolic{T} where {T}
    FRACTION_FLATTENER(x)
end

function fraction_iszero(x)
    !iscall(x) && return _iszero(x)
    ff = flatten_fractions(x)
    # fast path and then slow path
    return (any(_iszero, numerators(ff)) ||
    any(_iszero∘expand, numerators(ff)))::Bool
end

function fraction_isone(x)
    !iscall(x) && return _isone(x)
    _isone(simplify_fractions(flatten_fractions(x)))
end

function needs_div_rules(x)
    (isdiv(x) && !(unwrap_const(x.num) isa Number) && !(unwrap_const(x.den) isa Number)) ||
    (iscall(x) && operation(x) === (+) && count(has_div, arguments(x)) > 1) ||
    (iscall(x) && any(needs_div_rules, arguments(x)))
end

function has_div(x)
    return isdiv(x) || (iscall(x) && any(has_div, arguments(x)))
end
