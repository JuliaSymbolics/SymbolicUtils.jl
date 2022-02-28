import SIMDPolynomials
using SymbolicUtils
using Setfield
using Bijections
using TermInterface
using ConstructionBase
const SP = SIMDPolynomials

import SymbolicUtils: Symbolic, BasicSymbolic

struct SPolyForm{P, T} <: Symbolic{T}
    p::P
    pvar2sym::Bijection{Int,BasicSymbolic}   # @polyvar x --> @sym x  etc.
    sym2term::Dict{BasicSymbolic,BasicSymbolic} # Symbol("sin-$hash(sin(x+y))") --> sin(x+y) => sin(PolyForm(...))
    metadata
    function (::Type{SPolyForm{T}})(p, d1, d2, m=nothing) where {T}
        new{typeof(p), T}(p, d1, d2, m)
    end
end

function ConstructionBase.constructorof(s::Type{<:SPolyForm{X,T}}) where {X,T}
    function (args...)
        SPolyForm{T}(args...)
    end
end

function sgcd(x,y)
    x,y = SPolyForm((x,y))
    mpoly(p) = p isa MPoly ? p : MPoly(p)
    Setfield.@set x.p = gcd(mpoly(x.p), mpoly(y.p))
end

function SPolyForm(x)
    SPolyForm((x,))[1]
end

function SPolyForm(xs::Tuple)
    pvar2sym = Bijection{Int,BasicSymbolic}()
    sym2term = Dict{BasicSymbolic,BasicSymbolic}()
    ctr = Ref(0)
    xs′ = map(xs) do x
        mark_kernels!(x, pvar2sym, sym2term, ctr)
    end

    N = ctr[]
    pvars = Dict(sym => SP.PackedMonomial{N, 7}(i) for (i, sym) in pvar2sym)

    map(xs′) do x′
        SPolyForm{symtype(x)}(substitute(x′, pvars), pvar2sym, sym2term)
    end
end

function mark_kernels!(x, pvar2sym, sym2term, ctr)

    local_mark(y) = mark_kernels!(y, pvar2sym, sym2term, ctr)
    if istree(x)
        op = operation(x)
        if op in (+,*,^)
            return SymbolicUtils.Term{symtype(x)}(op,
                                    map(local_mark, unsorted_arguments(x)),
                                    metadata=metadata(x))
        else
            name = Symbol(string(op), "_", hash(x))

            @label lookup
            sym = Sym{symtype(x)}(name)
            if haskey(sym2term, sym)
                if isequal(sym2term[sym], x)
                    local_mark(sym)
                    return sym
                else # hash collision
                    name = Symbol(name, "_")
                    @goto lookup
                end
            end
        end
    elseif issym(x)
        sym2pvar = active_inv(pvar2sym)
        if haskey(sym2pvar, x)
            return x
        else
            pvar2sym[ctr[]] = x
            ctr[] += 1
            return x
        end
    elseif x isa Number
        return x
    else
        error("Wtf is $x")
    end
end

TermInterface.istree(x::Type{<:SPolyForm}) = true

isoneterm(x) = x isa Union{SP.AbstractMonomial,SP.AbstractTerm}
ispvar(x) = x isa SP.PackedMonomial && isone(sum(SP.exprs(a)))
TermInterface.operation(x::SPolyForm) = isoneterm(x.p) ? (*) : (+)

function TermInterface.arguments(x::SPolyForm)
    function resolve_var(x, i)
        sym = x.pvar2sym[i]
        get(x.sym2term, sym, sym)
    end

    if operation(x) == *
        # can be a term
        args = [resolve_var(x, i-1)^exp
         for (i, exp) in enumerate(SP.exps(x.p))
         if !iszero(exp)]

        x.p isa SP.Term && !isone(SP.coeff(x.p)) ?
            vcat(SP.coeff(x.p), args) : args
    else # +
        [(Setfield.@set x.p = t) for t in SP.terms(x.p)]
    end
end

Base.show(io::IO, x::SPolyForm) = SymbolicUtils.show_term(io, x)


#===
#
# nterms -- ^ + MPoly
# terms --> (x,)
# isterm --> true (Monom & Term) not for MPoly
#    ismonomial
#    coeff  --> 1
#    monomial --> (Monom & Term
