export PolyForm, simplify_fractions
using Bijections
using DynamicPolynomials: PolyVar

"""
    PolyForm{T} <: Symbolic{T}

Abstracts a [MultivariatePolynomials.jl](https://juliaalgebra.github.io/MultivariatePolynomials.jl/stable/) as a SymbolicUtils expression and vice-versa.
We use this to hold polynomials in memory while doing `simplify_fractions`.
"""
struct PolyForm{T, M} <: Symbolic{T}
    p::MP.AbstractPolynomialLike
    pvar2sym::Bijection   # @polyvar x --> @sym x  etc.
    sym2term::Dict        # Symbol("sin-$hash(sin(x+y))") --> sin(x+y) => sin(PolyForm(...))
    metadata::M
end

Base.hash(p::PolyForm, u::UInt64) = xor(hash(p.p, u),  trunc(UInt, 0xbabacacababacaca))
Base.isequal(x::PolyForm, y::PolyForm) = isequal(x.p, y.p)

# We use the same PVAR2SYM bijection to maintain the PolyVar <-> Sym mapping,
# When all PolyForms go out of scope in a session, we allow it to free up memory and
# start over if necessary
const PVAR2SYM = Ref(WeakRef())
const SYM2TERM = Ref(WeakRef())
function get_pvar2sym()
    v = PVAR2SYM[].value
    if v === nothing
        d = Bijection{Any,Sym}()
        PVAR2SYM[] = WeakRef(d)
        return d
    else
        return v
    end
end

function get_sym2term()
    v = SYM2TERM[].value
    if v === nothing
        d = Dict{Sym,Any}()
        SYM2TERM[] = WeakRef(d)
        return d
    else
        return v
    end
end

function mix_dicts(p, q)
    p.pvar2sym !== q.pvar2sym && error("pvar2sym mappings don't match for $p and $q")
    p.sym2term !== q.sym2term && error("sym2term mappings don't match for $p and $q")

    p.pvar2sym, p.sym2term
end

# forward gcd
for f in [:gcd, :div]
    @eval begin
        Base.$f(x::PolyForm, y::PolyForm) = PolyForm($f(x.p, y.p), mix_dicts(x, y)...)
        Base.$f(x::Integer, y::PolyForm) = PolyForm($f(x, y.p), y.pvar2sym, y.sym2term)
        Base.$f(x::PolyForm, y::Integer) = PolyForm($f(x.p, y), x.pvar2sym, x.sym2term)
    end
end
_isone(p::PolyForm) = isone(p.p)

function polyize(x, pvar2sym, sym2term, vtype, pow)
    if istree(x)
        if !(symtype(x) <: Number)
            error("Cannot convert $x of symtype $(symtype(x)) into a PolyForm")
        end

        op = operation(x)
        args = arguments(x)

        local_polyize(y) = polyize(y, pvar2sym, sym2term, vtype, pow)

        if op == (+)
            return sum(local_polyize, args)
        elseif op == (*)
            return prod(local_polyize, args)
        elseif op == (^) && args[2] isa Integer && args[2] > 0
            @assert length(args) == 2
            return local_polyize(args[1])^(args[2])
        else
            # create a new symbol to store this

            name = Symbol(string(op), "-", hash(x))

            @label lookup
            sym = Sym{symtype(x)}(name)
            if haskey(sym2term, sym)
                if isequal(sym2term[sym][1], x)
                    return local_polyize(sym)
                else # hash collision
                    name = Symbol(name, "_")
                    @goto lookup
                end
            end

            sym2term[sym] = x => similarterm(x,
                                             op,
                                             map(a->PolyForm(a, pvar2sym, sym2term, vtype),
                                                 args), symtype(x))
            return local_polyize(sym)
        end
    elseif x isa Number
        return x
    elseif x isa Sym
        if haskey(active_inv(pvar2sym), x)
            return pvar2sym(x)
        end
        pvar = MP.similarvariable(vtype, nameof(x))
        pvar2sym[pvar] = x
        return pvar
    end
end

function PolyForm(x::Symbolic{<:Number},
        pvar2sym=get_pvar2sym(),
        sym2term=get_sym2term(),
        vtype=DynamicPolynomials.PolyVar{true};
        metadata=metadata(x))

    # Polyize and return a PolyForm
    p = polyize(x, pvar2sym, sym2term, vtype, pow)
    MP.isconstant(p) && return convert(Number, p)
    PolyForm{symtype(x), typeof(metadata)}(p, pvar2sym, sym2term, metadata)
end

function PolyForm(x::MP.AbstractPolynomialLike,
        pvar2sym=get_pvar2sym(),
        sym2term=get_sym2term(),
        metadata=nothing)
    # make number go
    PolyForm{Number, Nothing}(x, pvar2sym, sym2term, metadata)
end

PolyForm(x, args...;kw...) = x

istree(x::PolyForm) = true

operation(x::PolyForm) = MP.nterms(x.p) == 1 ? (*) : (+)

function arguments(x::PolyForm{T}) where {T}

    function is_var(v)
        MP.nterms(v) == 1 &&
        isone(MP.coefficient(MP.terms(v)[1])) &&
        MP.degree(MP.monomial(v)) == 1
    end

    function get_var(v)
        # must be called only after a is_var check
        MP.variable(MP.monomial(v))
    end

    function resolve(p)
        !is_var(p) && return p
        pvar = get_var(p)
        s = x.pvar2sym[pvar]
        haskey(x.sym2term, s) ? x.sym2term[s][2] : s
    end

    if MP.nterms(x.p) == 1
        MP.isconstant(x.p) && return [convert(Number, x.p)]
        c = MP.coefficient(x.p)
        t = MP.monomial(x.p)

        if !isone(c)
            [c, (unstable_pow(resolve(v), pow)
                        for (v, pow) in MP.powers(t) if !iszero(pow))...]
        else
            [unstable_pow(resolve(v), pow)
                    for (v, pow) in MP.powers(t) if !iszero(pow)]
        end
    else
        ts = MP.terms(x.p)
        return [MP.isconstant(t) ?
                convert(Number, t) :
                (is_var(t) ?
                 resolve(t) :
                 PolyForm{T, Nothing}(t, x.pvar2sym, x.sym2term, nothing)) for t in ts]
    end
end

Base.show(io::IO, x::PolyForm) = show_term(io, x)

"""
    expand(expr)

Expand expressions by distributing multiplication over addition, e.g.,
`a*(b+c)` becomes `ab+ac`.

`expand` uses replace symbols and non-algebraic expressions by variables of type
`variable_type` to compute the distribution using a specialized sparse
multivariate polynomials implementation.
`variable_type` can be any subtype of `MultivariatePolynomials.AbstractVariable`.
"""
expand(expr) = PolyForm(expr)


## Rational Polynomial form with Div

function polyform_factors(d::Div, pvar2sym, sym2term)
    make(xs) = map(xs) do x
        if x isa Pow && arguments(x)[2] isa Integer && arguments(x)[2] > 0
            Pow(PolyForm(arguments(x)[1], pvar2sym, sym2term), arguments(x)[2])
        else
            PolyForm(x, pvar2sym, sym2term)
        end
    end

    return make(numerators(d)), make(denominators(d))
end

_mul(xs...) = all(isempty, xs) ? 1 : *(Iterators.flatten(xs)...)

function simplify_fractions(d::Div)
    ns, ds = polyform_factors(d, get_pvar2sym(), get_sym2term())
    ns, ds = rm_gcds(ns, ds)
    if all(_isone, ds)
        return isempty(ns) ? 1 : _mul(ns)
    else
        return Div(_mul(ns), _mul(ds), true)
    end
end

function add_divs(x::Div, y::Div)
    x_num, x_den = polyform_factors(x, get_pvar2sym(), get_sym2term())
    y_num, y_den = polyform_factors(y, get_pvar2sym(), get_sym2term())

    Div(_mul(x_num, y_den) + _mul(x_den, y_num), _mul(x_den, y_den))
end

function simplify_fractions(x)
    isdiv(x) = x isa Div

    rules = [@acrule ~a::isdiv + ~b::isdiv => add_divs(~a,~b)
             @rule ~x::isdiv => simplify_fractions(~x)]

    Postwalk(RestartedChain(rules))(x)
end

flatten_pows(xs) = map(xs) do x
    x isa Pow ? Iterators.repeated(arguments(x)...) : (x,)
end |> Iterators.flatten |> a->collect(Any,a)

function rm_gcds(ns, ds)
    ns = flatten_pows(ns)
    ds = flatten_pows(ds)

    for i = 1:length(ns)
        for j = 1:length(ds)
            g = gcd(ns[i], ds[j])
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
