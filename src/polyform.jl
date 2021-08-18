export PolyForm

struct PolyForm{T, M} <: Symbolic{T}
    p::MP.AbstractPolynomialLike
    pvar2sym::Dict   # @polyvar x --> @sym x  etc.
    sym2term::Dict   # gensym("sin") --> sin(PolyForm(...))
    metadata::M
end

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
            name = gensym(string(op))

            sym = Sym{symtype(x)}(name)
            sym2term[sym] = similarterm(x,
                                        op,
                                        map(a->PolyForm(a, pvar2sym, sym2term, vtype),
                                            args), symtype(x))
            return local_polyize(sym)
        end
    elseif x isa Number
        return x
    elseif x isa Sym
        pvar = MP.similarvariable(vtype, nameof(x))
        pvar2sym[pvar] = x
        return pvar
    end
end

function PolyForm(x::Symbolic{<:Number},
        pvar2sym=Dict{Any, Sym}(),
        sym2term=Dict{Sym, Any}(),
        vtype = DynamicPolynomials.PolyVar{true})

    # Polyize and return a PolyForm
    PolyForm{symtype(x)}(polyize(x, pvar2sym, sym2term, vtype),
                         pvar2sym, sym2term, metadata(x))
end

PolyForm(x, args...) = x

istree(x::PolyForm) = true

function operation(x::PolyForm)
    MP.nterms(x.p) == 1 ? (*) : (+)
end

function arguments(x::PolyForm{T}) where {T}

    function is_var(v)
        MP.nterms(v) == 1 &&
        isone(sum(x->abs(MP.degree(v, x)), MP.variables(MP.monomial(v))))
    end

    function resolve(pvar)
        s = x.pvar2sym[pvar]
        haskey(x.sym2term, s) ? x.sym2term[s] : s
    end

    if MP.nterms(x.p) == 1
        c = MP.coefficient(x.p)

        if !isone(c)
            return [c, (unstable_pow(resolve(v), pow)
                        for (v, pow) in MP.powers(MP.monomial(x.p)))...]
        else
            return [unstable_pow(resolve(v), pow)
                    for (v, pow) in MP.powers(MP.monomial(x.p))]
        end
    else
        ts = MP.terms(x.p)
        return [is_var(t) ? resolve(t) : PolyForm{T}(t, x.pvar2sym, x.sym2term) for t in ts]
    end
end

Base.show(io::IO, x::PolyForm) = show_term(io, x)

