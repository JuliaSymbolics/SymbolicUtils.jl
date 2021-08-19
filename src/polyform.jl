export PolyForm, simplify_fractions
using Bijections
using DynamicPolynomials: PolyVar

"""
    PolyForm{T} <: Symbolic{T}

A polynomial-normal form term.
"""
struct PolyForm{T, M} <: Symbolic{T}
    p::MP.AbstractPolynomialLike
    pvar2sym::Bijection   # @polyvar x --> @sym x  etc.
    sym2term::Dict        # Symbol("sin-$hash(sin(x+y))") --> sin(x+y) => sin(PolyForm(...))
    metadata::M
end

Base.hash(p::PolyForm, u::UInt64) = xor(hash(p.p, u),  0xbabacacababacaca)
Base.isequal(x::PolyForm, y::PolyForm) = isequal(x.p, y.p)

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
        pvar = _similarvariable(vtype, nameof(x), hash(x))
        pvar2sym[pvar] = x
        return pvar
    end
end

_similarvariable(::Type{PolyVar{true}}, name, id) = PolyVar{true}(String(name), id)
_similarvariable(T, name, id) = MT.similarvariable(T, name)

function PolyForm(x::Symbolic{<:Number},
        pvar2sym=Bijection{Any, Sym}(),
        sym2term=Dict{Sym, Any}(),
        vtype=DynamicPolynomials.PolyVar{true};
        metadata=metadata(x))

    # Polyize and return a PolyForm
    p = polyize(x, pvar2sym, sym2term, vtype, pow)
    PolyForm{symtype(x), typeof(metadata)}(p, pvar2sym, sym2term, metadata)
end

function PolyForm(x::MP.AbstractPolynomialLike,
        pvar2sym=Bijection{Any, Sym}(),
        sym2term=Dict{Sym, Any}(),
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

function simplify_fractions(d::Div)
    pvar2sym = Bijection{Any, Sym}()
    sym2term = Dict{Sym, Any}()

    ns, ds = polyform_factors(d, pvar2sym, sym2term)
    ns, ds = rm_gcds(ns, ds)
    if all(_isone, ds)
        return isempty(ns) ? 1 : *(ns...)
    else
        return Div(*(ns...), *(ds...), true)
    end
end

function add_divs(x::Div, y::Div)
    pvar2sym = Bijection{Any, Sym}()
    sym2term = Dict{Sym, Any}()

    x_num, x_den = polyform_factors(x, pvar2sym, sym2term)
    y_num, y_den = polyform_factors(y, pvar2sym, sym2term)

    Div(*(x_num..., y_den...) + *(x_den..., y_num...), *(x_den..., y_den...))
end

function simplify_fractions(x)
    isdiv(x) = x isa Div

    rules = [@acrule ~a::isdiv + ~b::isdiv => add_divs(~a,~b)
             @rule ~x::isdiv => simplify_fractions(~x)]

    Postwalk(RestartedChain(rules))(x)
end

flatten_pows(xs) = map(xs) do x
    x isa Pow ? Iterators.repeated(arguments(x)...) : (x,)
end |> Iterators.flatten |> collect

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
