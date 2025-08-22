export simplify_fractions, quick_cancel, flatten_fractions

to_poly!(_, expr, _...) = MA.operate!(+, zeropoly(typeof(expr)), expr)
function to_poly!(poly_to_bs::Dict, expr::BasicSymbolic{T}, recurse = true)::Union{PolyVarT, PolynomialT{T}} where {T}
    @match expr begin
        BSImpl.Const(; val) => to_poly!(poly_to_bs, val, recurse)
        BSImpl.Sym(;) => begin
            pvar = basicsymbolic_to_partial_polyvar(expr)
            get!(poly_to_bs, pvar, expr)
            return pvar
        end
        BSImpl.Polyform(; poly, partial_polyvars, vars) => begin
            pvars = MP.variables(poly)
            subs = typeof(poly)[]
            for var in vars
                push!(subs, to_poly!(poly_to_bs, var))
            end
            poly = poly(pvars => subs)
            if poly isa PolynomialT{T}
                return poly
            end
            return PolynomialT{T}(Vector{T}(MP.coefficients(poly)), MP.monomials(poly))
        end
        BSImpl.Term(; f, args) => begin
            if f === (^) && args[2] isa Real && isinteger(args[2])
                base, exp = args
                poly = to_poly!(poly_to_bs, base)
                return if poly isa PolyVarT
                    isone(exp) && return poly
                    mv = DP.MonomialVector{PolyVarOrder, MonomialOrder}([poly], [Int[exp]])
                    PolynomialT{T}(T[one(T)], mv)
                else
                    PolynomialT{T}(Vector{T}(MP.coefficients(poly)), MP.monomials(poly))
                end
            elseif f === (*) || f === (+)
                arg1, restargs = Iterators.peel(args)
                poly = to_poly!(poly_to_bs, arg1)
                if !(poly isa PolynomialT{T})
                    _poly = zeropoly(T)
                    MA.operate!(+, _poly, poly)
                    poly = _poly
                end
                for arg in restargs
                    MA.operate!(*, poly, to_poly!(poly_to_bs, arg))
                end
                return poly
            else
                if recurse
                    expr = BSImpl.Term{symtype(expr)}(f, map(expand, args))
                end
                pvar = basicsymbolic_to_partial_polyvar(expr)
                get!(poly_to_bs, pvar, expr)
                return pvar
            end
        end
        BSImpl.Div(; num, den) => begin
            if recurse
                expr = BSImpl.Div{symtype(expr)}(expand(num), expand(den), false)
            end
            pvar = basicsymbolic_to_partial_polyvar(expr)
            get!(poly_to_bs, pvar, expr)
            return pvar
        end
    end
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
function expand(expr)
    if !(expr isa BasicSymbolic)
        return expr
    end
    iscall(expr) || return expr
    poly_to_bs = Dict{PolyVarT, BasicSymbolic}()
    partial_poly = to_poly!(poly_to_bs, expr)
    partial_pvars = MP.variables(partial_poly)
    vars = SmallV{BasicSymbolic}()
    pvars = PolyVarT[]
    sizehint!(vars, length(partial_pvars))
    sizehint!(pvars, length(partial_pvars))
    for ppvar in partial_pvars
        var = poly_to_bs[ppvar]
        push!(vars, var)
        push!(pvars, basicsymbolic_to_polyvar(var))
    end
    poly = swap_polynomial_vars(partial_poly, pvars)
    return Polyform{symtype(expr)}(poly)
end

## Rational Polynomial form with Div

_mul(xs...) = all(isempty, xs) ? 1 : *(Iterators.flatten(xs)...)

function simplify_div(d)
    isdiv(d) || return d
    d.simplified && return d
    num, den = simplify_div(symtype(d), d.num, d.den)
    return simplify_fractions(num) / simplify_fractions(den)
end

function canonicalize_coeffs!(coeffs::Vector{T}) where {T}
    Int <: T || return
    T <: Integer && return
    for i in eachindex(coeffs)
        v = coeffs[i]
        isinteger(v) || continue
        coeffs[i] = Int(v)
    end
    return
end
canonicalize_coeffs!(_) = nothing

function simplify_div(::Type{T}, num, den) where {T}
    poly_to_bs = Dict{PolyVarT, BasicSymbolic}()
    partial_poly1 = to_poly!(poly_to_bs, num, false)
    partial_poly2 = to_poly!(poly_to_bs, den, false)
    factor = gcd(partial_poly1, partial_poly2)
    if isone(factor)
        return num, den
    end
    # NOTE: This does not mutate `partial_poly1` to be the result, it just
    # uses it as buffer. The result is the returned value.
    partial_poly1 = MP.div_multiple(partial_poly1, factor, MA.IsMutable())
    partial_poly2 = MP.div_multiple(partial_poly2, factor, MA.IsMutable())
    canonicalize_coeffs!(MP.coefficients(partial_poly1))
    canonicalize_coeffs!(MP.coefficients(partial_poly2))
    pvars1 = MP.variables(partial_poly1)
    pvars2 = MP.variables(partial_poly2)
    vars1 = [poly_to_bs[v] for v in pvars1]
    vars2 = [poly_to_bs[v] for v in pvars2]
    return subs_poly(partial_poly1, vars1), subs_poly(partial_poly2, vars2)
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
function quick_cancel(d::BSImpl.Type{T}) where {T}
    iscall(d) || return d
    op = operation(d)
    if op === (^)
        base, exp = arguments(d)
        base isa BasicSymbolic || return d
        isdiv(base) || return d
        num, den = quick_cancel(base.num, base.den)
        return Div{T}(num ^ exp, den ^ exp, false)
    elseif op === (/)
        num, den = arguments(d)
        num, den = quick_cancel(num, den)
        return Div{T}(num, den, false)
    else
        return d
    end
end

function quick_cancel(x, y)
    opx = iscall(x) ? operation(x) : nothing
    opy = iscall(y) ? operation(y) : nothing
    if opx === (^) && opy === (^)
        return quick_powpow(x, y)
    elseif opx === (*) && opy === (^)
        return quick_mulpow(x, y)
    elseif opx === (^) && opy === (*)
        return reverse(quick_mulpow(y, x))
    elseif opx === (*) && opy === (*)
        return quick_mulmul(x, y)
    elseif opx === (^)
        return quick_pow(x, y)
    elseif opy === (^)
        return reverse(quick_pow(y, x))
    elseif opx === (*)
        return quick_mul(x, y)
    elseif opy === (*)
        return reverse(quick_mul(y, x))
    elseif isequal(x, y)
        return 1, 1
    else
        return x, y
    end
end

# ispow(x) case
function quick_pow(x, y)
    base, exp = arguments(x)
    exp isa Number || return (x, y)
    isequal(base, y) && exp >= 1 ? (base ^ (exp - 1), 1) : (x, y)
end

# Double Pow case
function quick_powpow(x, y)
    base1, exp1 = arguments(x)
    base2, exp2 = arguments(y)
    isequal(base1, base2) || return x, y
    !(exp1 isa Number && exp2 isa Number) && return (x, y)
    if exp1 > exp2
        return base1 ^ (exp1 - exp2), 1
    elseif exp1 == exp2
        return 1, 1
    else # exp1 < exp2
        return 1, base2 ^ (exp2 - exp1)
    end
end

# ismul(x)
function quick_mul(x, y)
    yy = BSImpl.Term{symtype(y)}(^, ArgsT((y, 1)))
    newx, newy = quick_mulpow(x, yy)
    return isequal(newy, yy) ? (x, y) : (newx, newy)
end

# mul, pow case
function quick_mulpow(x, y)
    base, exp = arguments(y)
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
    argexp isa Number || return x, y
    # cheat by mutating `args` to avoid allocating
    args = parent(args)
    oldval = args[idx]
    if argexp > exp
        args[idx] = argbase ^ (argexp - exp)
        result = mul_worker(args), 1
    elseif argexp == exp
        args[idx] = 1
        result = mul_worker(args), 1
    else
        args[idx] = 1
        result = mul_worker(args), base ^ (exp - argexp)
    end
    args[idx] = oldval
    return result
end

# Double mul case
function quick_mulmul(x, y)
    yargs = arguments(y)
    for (i, arg) in enumerate(yargs)
        newx, newarg = quick_cancel(x, arg)
        isequal(arg, newarg) && continue
        if yargs isa ROArgsT
            yargs = copy(parent(yargs))
        end
        yargs[i] = newarg
        x = newx
    end
    if yargs isa ROArgsT
        return x, y
    else
        return x, mul_worker(yargs)
    end
end

function add_with_div(x)
    (!iscall(x) || operation(x) !== (+)) && return x
    aa = parent(arguments(x))
    !any(isdiv, aa) && return x # no rewrite necessary

    # find and multiply all denominators
    dens = ArgsT()
    for a in aa
        isdiv(a) || continue
        push!(dens, a.den)
    end
    T = symtype(x)
    den = mul_worker(T, dens)

    # add all numerators
    div_idx = 1
    nums = ArgsT()
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
    num = add_worker(nums)

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
function simplify_fractions(x)

    x = QUICK_CANCELER(x)

    !needs_div_rules(x) && return x

    return FRAC_SIMPLIFIER(x)
end

const FRACTION_FLATTENER = Rewriters.Fixpoint(Rewriters.Postwalk(add_with_div))

"""
    flatten_fractions(x)

Flatten nested fractions that are added together.

```julia
julia> flatten_fractions((1+(1+1/a)/a)/a)
(1 + a + a^2) / (a^3)
```
"""
function flatten_fractions(x)
    FRACTION_FLATTENER(x)
end

function fraction_iszero(x)
    !iscall(x) && return _iszero(x)
    ff = flatten_fractions(x)
    # fast path and then slow path
    any(_iszero, numerators(ff)) ||
    any(_iszero∘expand, numerators(ff))
end

function fraction_isone(x)
    !iscall(x) && return _isone(x)
    _isone(simplify_fractions(flatten_fractions(x)))
end

function needs_div_rules(x)
    (isdiv(x) && !(x.num isa Number) && !(x.den isa Number)) ||
    (iscall(x) && operation(x) === (+) && count(has_div, arguments(x)) > 1) ||
    (iscall(x) && any(needs_div_rules, arguments(x)))
end

function has_div(x)
    return isdiv(x) || (iscall(x) && any(has_div, arguments(x)))
end

