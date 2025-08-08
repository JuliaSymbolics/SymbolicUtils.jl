export simplify_fractions, quick_cancel, flatten_fractions

to_poly!(_, expr, _...) = MA.operate!(+, zeropoly(typeof(expr)), expr)
function to_poly!(poly_to_bs::Dict, expr::BasicSymbolic{T}, recurse = true)::Union{PolyVarT, PolynomialT{T}} where {T}
    @match expr begin
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
            return MP.polynomial(poly(pvars => subs), T)
        end
        BSImpl.Term(; f, args) => begin
            if f === (^) && args[2] isa Real && isinteger(args[2])
                base, exp = args
                return MP.polynomial(to_poly!(poly_to_bs, base) ^ Int(exp), T)
            elseif f === (*) || f === (+)
                arg1, restargs = Iterators.peel(args)
                poly = to_poly!(poly_to_bs, arg1)
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

function polyform_factors(d, pvar2sym, sym2term)
    make(xs) = map(xs) do x
        if ispow(x) && x.exp isa Integer && x.exp > 0
            # here we do want to recurse one level, that's why it's wrong to just
            # use Fs = Union{typeof(+), typeof(*)} here.
            Pow(PolyForm(x.base; pvar2sym, sym2term), x.exp)
        else
            PolyForm(x; pvar2sym, sym2term)
        end
    end

    return make(numerators(d)), make(denominators(d))
end

_mul(xs...) = all(isempty, xs) ? 1 : *(Iterators.flatten(xs)...)

function simplify_div(d)
    d.simplified && return d
    ns, ds = polyform_factors(d, get_pvar2sym(), get_sym2term())
    ns, ds = rm_gcds(ns, ds)
    if all(_isone, ds)
        return isempty(ns) ? 1 : simplify_fractions(_mul(ns))
    else
        Div(simplify_fractions(_mul(ns)), simplify_fractions(_mul(ds)), false)
    end
end

function frac_maketerm(T, f, args, metadata)
    # TODO add stype to T?
    if f in (*, /, \, +, -)
        f(args...)
    elseif f == (^)
        if args[2] isa Integer && args[2] < 0
            1/((args[1])^(-args[2]))
        else
            args[1]^args[2]
        end
    else
        maketerm(T, f, args, metadata)
    end
end

"""
    simplify_fractions(x; polyform=false)

Find `Div` nodes and simplify them by cancelling a set of factors of numerators
and denominators. If `polyform=true` the factors which were converted into PolyForm
for the purpose of finding polynomial GCDs will be left as they are.
Note that since PolyForms have different `hash`es than SymbolicUtils expressions,
`substitute` may not work if `polyform=true`
"""
function simplify_fractions(x; polyform=false)

    x = Postwalk(quick_cancel)(x)

    !needs_div_rules(x) && return x

    sdiv(a) = isdiv(a) ? simplify_div(a) : a

    expr = Postwalk(sdiv ∘ quick_cancel,
                    maketerm=frac_maketerm)(Postwalk(add_with_div,
                                                           maketerm=frac_maketerm)(x))

    polyform ? expr : unpolyize(expr)
end

function add_with_div(x, flatten=true)
    (!iscall(x) || operation(x) != (+)) && return x
    aa = parent(arguments(x))
    !any(isdiv, aa) && return x # no rewrite necessary

    # find and multiply all denominators
    dens = ArgsT()
    for a in aa
        isdiv(a) || continue
        push!(dens, a.den)
    end
    den = mul_worker(dens)

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
            _num = mul_worker(dens)
            dens[div_idx] = _den
            div_idx += 1
        else
            _num = den * a
        end
        push!(nums, _num)
    end
    num = add_worker(nums)

    if flatten
        num, den = quick_cancel(num, den)
    end
    return num / den
end
"""
    flatten_fractions(x)

Flatten nested fractions that are added together.

```julia
julia> flatten_fractions((1+(1+1/a)/a)/a)
(1 + a + a^2) / (a^3)
```
"""
function flatten_fractions(x)
    Fixpoint(Postwalk(add_with_div))(x)
end

function fraction_iszero(x)
    !iscall(x) && return _iszero(x)
    old_hc = ENABLE_HASHCONSING[]
    ENABLE_HASHCONSING[] = false
    ff = flatten_fractions(x)
    ENABLE_HASHCONSING[] = old_hc
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

flatten_pows(xs) = map(xs) do x
    ispow(x) ? Iterators.repeated(arguments(x)...) : (x,)
end |> Iterators.flatten |> a->collect(Any,a)

# coefftype(x::PolyForm) = coefftype(x.p)
coefftype(x::MP.AbstractPolynomialLike{T}) where {T} = T
coefftype(x) = typeof(x)

const MaybeGcd = Union{#=PolyForm, =#MP.AbstractPolynomialLike, Integer}
_gcd(x::MaybeGcd, y::MaybeGcd) = (coefftype(x) <: Complex || coefftype(y) <: Complex) ? 1 : gcd(x, y)
_gcd(x, y) = 1


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
    @match d begin
        # BSImpl.Pow(; base, exp) => begin
        #     base isa BSImpl.Type || return d
        #     MData.isa_variant(base, BSImpl.Div) || return d
        #     n, d = quick_cancel((base.num ^ exp), (base.den ^ exp))
        #     return Div{T}(n, d, false)
        # end
        # BSImpl.AddOrMul(; variant) && if variant == AddMulVariant.MUL && any(isdiv, arguments(d)) end => begin
        #     return mul_worker(arguments(d))
        # end
        BSImpl.Div(; num, den) => begin
            num, den = quick_cancel(num, den)
            return Div(num, den, false)
        end
        _ => return d
    end
end

function quick_cancel(x, y)
    if ispolyform(x) || ispolyform(y)
        return x, y
    end
    if ispow(x) && ispow(y)
        return quick_powpow(x, y)
    elseif ismul(x) && ispow(y)
        return quick_mulpow(x, y)
    elseif ispow(x) && ismul(y)
        return reverse(quick_mulpow(y, x))
    elseif ismul(x) && ismul(y)
        return quick_mulmul(x, y)
    elseif ispow(x)
        return quick_pow(x, y)
    elseif ispow(y)
        return reverse(quick_pow(y, x))
    elseif ismul(x)
        return quick_mul(x, y)
    elseif ismul(y)
        return reverse(quick_mul(y, x))
    else
        return isequal(x, y) ? (1,1) : (x, y)
    end
end

# ispow(x) case
function quick_pow(x, y)
    x.exp isa Number || return (x, y)
    isequal(x.base, y) && x.exp >= 1 ? (Pow{symtype(x)}(x.base, x.exp - 1),1) : (x, y)
end

# Double Pow case
function quick_powpow(x, y)
    if isequal(x.base, y.base)
        !(x.exp isa Number && y.exp isa Number) && return (x, y)
        if x.exp > y.exp
            return Pow{symtype(x)}(x.base, x.exp-y.exp), 1
        elseif x.exp == y.exp
            return 1, 1
        else # x.exp < y.exp
            return 1, Pow{symtype(y)}(y.base, y.exp-x.exp)
        end
    end
    return x, y
end

# ismul(x)
function quick_mul(x, y)
    if haskey(x.dict, y) && x.dict[y] >= 1
        d = copy(x.dict)
        if d[y] > 1
            d[y] -= 1
        elseif d[y] == 1
            delete!(d, y)
        else
            error("Can't reach")
        end

        return Mul{symtype(x)}(x.coeff, d), 1
    else
        return x, y
    end
end

# mul, pow case
function quick_mulpow(x, y)
    y.exp isa Number || return (x, y)
    if haskey(x.dict, y.base)
        d = copy(x.dict)
        if x.dict[y.base] > y.exp
            d[y.base] -= y.exp
            den = 1
        elseif x.dict[y.base] == y.exp
            delete!(d, y.base)
            den = 1
        else
            den = Pow{symtype(y)}(y.base, y.exp-d[y.base])
            delete!(d, y.base)
        end
        return Mul{symtype(x)}(x.coeff, d), den
    else
        return x, y
    end
end

# Double mul case
function quick_mulmul(x, y)
    num_dict, den_dict = _merge_div(x.dict, y.dict)
    Mul{symtype(x)}(x.coeff, num_dict), Mul{symtype(y)}(y.coeff, den_dict)
end

function _merge_div(ndict, ddict)
    num = copy(ndict)
    den = copy(ddict)
    for (k, v) in den
        if haskey(num, k)
            nk = num[k]
            if nk > v
                num[k] -= v
                delete!(den, k)
            elseif nk == v
                delete!(num, k)
                delete!(den, k)
            else
                den[k] -= nk
                delete!(num, k)
            end
        end
    end
    num, den
end

function rm_gcds(ns, ds)
    ns = flatten_pows(ns)
    ds = flatten_pows(ds)

    for i = 1:length(ns)
        for j = 1:length(ds)
            g = _gcd(ns[i], ds[j])
            if !_isone(g)
                ns[i] = div(ns[i], g)
                ds[j] = div(ds[j], g)
            end
        end
    end

    filter!(!_isone, ns)
    filter!(!_isone, ds)

    ns,ds
end
