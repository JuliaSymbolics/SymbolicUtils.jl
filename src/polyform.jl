export PolyForm, simplify_fractions
using Bijections

struct PolyForm{T, M} <: Symbolic{T}
    p::MP.AbstractPolynomialLike
    pvar2sym::Bijection   # @polyvar x --> @sym x  etc.
    sym2term::Dict        # Symbol("sin-$hash(sin(x+y))") --> sin(x+y) => sin(PolyForm(...))
    metadata::M
end

function mix_dicts(p, q)
    (p.pvar2sym === q.pvar2sym ? p.pvar2sym : merge(p.pvar2sym, q.pvar2sym),
     p.sym2term === q.sym2term ? p.sym2term : merge(p.sym2term, q.sym2term))
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

function polyize(x, pvar2sym, sym2term, vtype)
    if istree(x)
        if !(symtype(x) <: Number)
            error("Cannot convert $x of symtype $(symtype(x)) into a PolyForm")
        end

        op = operation(x)
        args = arguments(x)

        local_polyize(y) = polyize(y, pvar2sym, sym2term, vtype)

        if op == (+)
            return sum(local_polyize, args)
        elseif op == (*)
            return prod(local_polyize, args)
        elseif op == (^) && args[2] isa Integer
            @assert length(args) == 2
            return local_polyize(args[1])^(args[2])
        else
            # create a new symbol to store this

            name = Symbol(string(op), "-", hash(x))

            @label lookup
            sym = Sym{symtype(x)}(name)
            if haskey(sym2term, sym)
                if isequal(sym2term[sym][1], x)
                    return pvar2sym(sym)
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
        pvar2sym=Bijection{Any, Sym}(),
        sym2term=Dict{Sym, Any}(),
        vtype=DynamicPolynomials.PolyVar{true};
        metadata=metadata(x))

    # Polyize and return a PolyForm
    PolyForm{symtype(x), typeof(metadata)}(polyize(x, pvar2sym, sym2term, vtype),
                                           pvar2sym, sym2term, metadata)
end

function PolyForm(x::MP.AbstractPolynomialLike,
        pvar2sym=Bijection{Any, Sym}(),
        sym2term=Dict{Sym, Any}(),
        metadata=nothing)
    # make number go
    PolyForm{Number, Nothing}(x, pvar2sym, sym2term, metadata)
end

PolyForm(x, args...) = x

istree(x::PolyForm) = true

operation(x::PolyForm) = MP.nterms(x.p) == 1 ? (*) : (+)

function arguments(x::PolyForm{T}) where {T}

    function is_var(v)
        MP.nterms(v) == 1 && isone(MP.coefficient(MP.terms(v)[1])) &&
        isone(sum(x->abs(MP.degree(v, x)), MP.variables(MP.monomial(v))))
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
        c = MP.coefficient(x.p)

        if !isone(c)
            [c, (unstable_pow(resolve(v), pow)
                        for (v, pow) in MP.powers(MP.monomial(x.p)) if !iszero(pow))...]
        else
            [unstable_pow(resolve(v), pow)
                    for (v, pow) in MP.powers(MP.monomial(x.p)) if !iszero(pow)]
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

function polyform_factors(d::Div)
    pvar2sym = Bijection{Any, Sym}()
    sym2term = Dict{Sym, Any}()

    ns = map(x->PolyForm(x, pvar2sym, sym2term), d.num)
    ds = map(x->PolyForm(x, pvar2sym, sym2term), d.den)

    return Div(ns, ds, true)
end

function simplify_fractions(d::Div)
    p = polyform_factors(d)
    ns = p.num
    ds = p.den
    rm_gcd!(ns, ds)
    if all(_isone, ds)
        return isempty(ns) ? 1 : *(ns...)
    else
        return Div(ns, ds, true)
    end
end

function add_divs(x::Div, y::Div)
    x = polyform_factors(x)
    y = polyform_factors(y)

    Div([prod(x.num) * prod(y.den) + prod(x.den) * prod(y.num)], vcat(x.den, y.den))
end

function simplify_fractions(x)
    isdiv(x) = x isa Div

    rules = [@acrule ~a::isdiv + ~b::isdiv => add_divs(~a,~b)
             @rule ~x::isdiv => simplify_fractions(~x)]

    Postwalk(RestartedChain(rules))(x)
end

function rm_gcd!(ns, ds)
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

    nothing
end
