export simplify_fractions, quick_cancel, flatten_fractions

to_poly!(::AbstractDict, ::AbstractDict, expr, ::Bool) = MA.operate!(+, zeropoly(), expr)
function to_poly!(poly_to_bs::AbstractDict, bs_to_poly::AbstractDict, expr::BasicSymbolic{T}, recurse::Bool = true)::Union{PolyVarT, PolynomialT} where {T}
    type = symtype(expr)
    @match expr begin
        BSImpl.Const(; val) => to_poly!(poly_to_bs, bs_to_poly, val, recurse)
        BSImpl.Sym(;) => begin
            pvar = basicsymbolic_to_polyvar(bs_to_poly, expr)
            get!(poly_to_bs, pvar, expr)
            return pvar
        end
        BSImpl.AddMul(; coeff, dict, variant) => begin
            @match variant begin
                AddMulVariant.ADD => begin
                    poly = zeropoly()
                    MA.operate!(+, poly, MA.copy_if_mutable(coeff))
                    for (k, v) in dict
                        tpoly = to_poly!(poly_to_bs, bs_to_poly, k, recurse)
                        if tpoly isa PolyVarT
                            tpoly = tpoly * v
                        else
                            MA.operate!(*, tpoly, v)
                        end
                        MA.operate!(+, poly, tpoly)
                    end
                    return poly
                end
                AddMulVariant.MUL => begin
                    poly = onepoly()
                    MA.operate!(*, poly, MA.copy_if_mutable(coeff))
                    for (k, v) in dict
                        if safe_isinteger(v)
                            tpoly = to_poly!(poly_to_bs, bs_to_poly, k, recurse) ^ Int(v)
                        else
                            tpoly = to_poly!(poly_to_bs, bs_to_poly, k ^ v, recurse)
                        end
                        MA.operate!(*, poly, tpoly)
                    end
                    return poly
                end
            end
        end
        BSImpl.Term(; f, args) => begin
            if f === (^) && isconst(args[2]) && (exp = unwrap_const(args[2]); exp isa Real) && safe_isinteger(exp)
                base = args[1]
                poly = to_poly!(poly_to_bs, bs_to_poly, base)
                if poly isa PolyVarT
                    isone(exp) && return poly
                    mv = DP.MonomialVector{PolyVarOrder, MonomialOrder}([poly], [Int[exp]])
                    return PolynomialT(PolyCoeffT[1], mv)
                end
                poly = poly ^ Int(exp)
                new_expr = from_poly(poly_to_bs, poly)
                if !isequal(expr, new_expr)
                    poly = to_poly!(poly_to_bs, bs_to_poly, from_poly(poly_to_bs, poly), recurse)
                end
                return poly
            elseif f === (*) || f === (+)
                arg1, restargs = Iterators.peel(args)
                poly = to_poly!(poly_to_bs, bs_to_poly, arg1)
                if !(poly isa PolynomialT)
                    _poly = zeropoly()
                    MA.operate!(+, _poly, poly)
                    poly = _poly
                end
                for arg in restargs
                    MA.operate!(f, poly, to_poly!(poly_to_bs, bs_to_poly, arg))
                end
                return poly
            else
                if recurse
                    expr = BSImpl.Term{T}(f, map(expand, args); type)
                end
                pvar = basicsymbolic_to_polyvar(bs_to_poly, expr)
                get!(poly_to_bs, pvar, expr)
                return pvar
            end
        end
        BSImpl.Div(; num, den) => begin
            if isconst(den)
                npoly = to_poly!(poly_to_bs, bs_to_poly, num, recurse)
                den = unwrap_const(den)
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
                expr = BSImpl.Div{T}(expand(num), expand(den), false; type)
            end
            pvar = basicsymbolic_to_polyvar(bs_to_poly, expr)
            get!(poly_to_bs, pvar, expr)
            return pvar
        end
    end
end

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
    poly_to_bs = Dict{PolyVarT, BasicSymbolic{T}}()
    bs_to_poly = Dict{BasicSymbolic{T}, PolyVarT}()
    partial_poly = to_poly!(poly_to_bs, bs_to_poly, expr, recurse)
    return from_poly(poly_to_bs, partial_poly)
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
        coeffs[i] = Int(v)
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
    if all_int
        return DP.Polynomial(Integer.(MP.coefficients(p)), MP.monomials(p))
    elseif all_rat
        return DP.Polynomial(rationalize.(MP.coefficients(p)), MP.monomials(p))
    elseif any_complex
        return DP.Polynomial((complex ∘ float).(MP.coefficients(p)), MP.monomials(p))
    else
        return DP.Polynomial(float.(MP.coefficients(p)), MP.monomials(p))
    end
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
    poly_to_bs = Dict{PolyVarT, BasicSymbolic{T}}()
    bs_to_poly = Dict{BasicSymbolic{T}, PolyVarT}()
    partial_poly1 = to_poly!(poly_to_bs, bs_to_poly, num, false)
    partial_poly2 = to_poly!(poly_to_bs, bs_to_poly, den, false)
    factor = safe_gcd(partial_poly1, partial_poly2)
    if isone(factor)
        return num, den
    end
    # NOTE: This does not mutate `partial_poly1` to be the result, it just
    # uses it as buffer. The result is the returned value.
    partial_poly1 = MP.div_multiple(partial_poly1, factor, MA.IsMutable())
    partial_poly2 = MP.div_multiple(partial_poly2, factor, MA.IsMutable())
    canonicalize_coeffs!(MP.coefficients(partial_poly1))
    canonicalize_coeffs!(MP.coefficients(partial_poly2))
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
    type = symtype(d)
    if op === (^)
        base, exp = arguments(d)
        isconst(base) && return d
        isdiv(base) || return d
        num, den = quick_cancel(base.num, base.den)
        return Div{T}(num ^ exp, den ^ exp, false; type)
    elseif op === (/)
        num, den = arguments(d)
        num, den = quick_cancel(num, den)
        return Div{T}(num, den, false; type)
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
    args = arguments(x)
    idx = 0
    argbase = argexp = nothing
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
    iszero(idx) && return x, y
    argexp = unwrap_const(argexp)
    argexp isa Number || return x, y
    # cheat by mutating `args` to avoid allocating
    args = parent(args)
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
        _ => _unreachable()
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

```julia
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

