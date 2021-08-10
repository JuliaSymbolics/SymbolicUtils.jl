# Polynomial Normal Form

"""
    labels!(dict, t)

Find all terms that are not + and * and replace them
with a symbol, store the symbol => term mapping in `dict`.
"""
function labels! end

# Turn a Term into a multivariate polynomial
function labels!(dicts, t::Sym,  variable_type::Type)
    sym2term, term2sym = dicts
    if !haskey(term2sym, t)
        sym2term[t] = t
        term2sym[t] = t
    end
    return t
end

function labels!(dicts, t, variable_type::Type)
    if t isa Number
        return t
    elseif istree(t) && (operation(t) == (*) || operation(t) == (+) || operation(t) == (-))
        tt = arguments(t)
        return similarterm(t, operation(t), map(x->labels!(dicts, x, variable_type), tt), symtype(t))
    elseif istree(t) && operation(t) == (^) && length(arguments(t)) > 1 && isnonnegint(arguments(t)[2])
        return similarterm(t, operation(t), map(x->labels!(dicts, x, variable_type), arguments(t)), symtype(t))
    else
        sym2term, term2sym = dicts
        if haskey(term2sym, t)
            return term2sym[t]
        end
        if istree(t)
            tt = arguments(t)
            sym = Sym{symtype(t)}(gensym(nameof(operation(t))))
            dicts2 = _dicts(dicts[2])
            sym2term[sym] = similarterm(t, operation(t),
                                        map(x->to_mpoly(x, variable_type, dicts)[1], arguments(t)),
                                        symtype(t))
        else
            sym = Sym{symtype(t)}(gensym("literal"))
            sym2term[sym] = t
        end

        term2sym[t] = sym

        return sym
    end
end

ismpoly(x) = x isa MP.AbstractPolynomialLike || x isa Number
isnonnegint(x) = x isa Integer && x >= 0

_dicts(t2s=OrderedDict{Any, Sym}()) = (OrderedDict{Sym, Any}(), t2s)

let
    mpoly_preprocess = [@rule(identity(~x) => ~x)
                        @rule(zero(~x) => 0)
                        @rule(one(~x) => 1)]

    simterm(x, f, args;metadata=nothing) = similarterm(x,f,args, symtype(x); metadata=metadata)
    mpoly_rules = [@rule(~x::ismpoly - ~y::ismpoly => ~x + -1 * (~y))
                   @rule(-(~x) => -1 * ~x)
                   @acrule(~x::ismpoly + ~y::ismpoly => ~x + ~y)
                   @rule(+(~x) => ~x)
                   @acrule(~x::ismpoly * ~y::ismpoly => ~x * ~y)
                   @rule(*(~x) => ~x)
                   @rule((~x::ismpoly)^(~a::isnonnegint) => (~x)^(~a))]
    global const MPOLY_CLEANUP = Fixpoint(Postwalk(PassThrough(RestartedChain(mpoly_preprocess)), similarterm=simterm))
    MPOLY_MAKER = Fixpoint(Postwalk(PassThrough(RestartedChain(mpoly_rules)), similarterm=simterm))

    global to_mpoly
    function to_mpoly(t, variable_type::Type=DynamicPolynomials.PolyVar{true}, dicts=_dicts())
        # term2sym is only used to assign the same
        # symbol for the same term -- in other words,
        # it does common subexpression elimination
        t = MPOLY_CLEANUP(t)
        sym2term, term2sym = dicts
        labeled = labels!((sym2term, term2sym), t, variable_type)

        if isempty(sym2term)
            return MPOLY_MAKER(labeled), Dict{Sym,Any}()
        end

        ks = sort(collect(keys(sym2term)), lt=<ₑ)
        vars = MP.similarvariable.(variable_type, nameof.(ks))

        replace_with_poly = Dict{Sym,eltype(vars)}(zip(ks, vars))
        t_poly = substitute(labeled, replace_with_poly, fold=false)
        MPOLY_MAKER(t_poly), sym2term
    end
end

function to_term(reference, x, dict)
    syms = Dict(zip(string.(nameof.(keys(dict))), keys(dict)))
    dict = copy(dict)
    for (k, v) in dict
        dict[k] = _to_term(reference, v, dict, syms)
    end
    return _to_term(reference, x, dict, syms)
    #return substitute(t, dict, fold=false)
end

_to_term(reference, x::Number, dict, syms) = x
_to_term(reference, var::MP.AbstractVariable, dict, syms) = substitute(syms[MP.name(var)], dict, fold=false)
function _to_term(reference, mono::MP.AbstractMonomialLike, dict, syms)
    monics = [
        begin
            t = _to_term(reference, var, dict, syms)
            exp == 1 ? t : t^exp
        end
        for (var, exp) in MP.powers(mono) if !iszero(exp)
    ]
    if length(monics) == 1
        return monics[1]
    elseif isempty(monics)
        return 1
    else
        return similarterm(reference, *, monics, symtype(reference))
    end
end

function _to_term(reference, term::MP.AbstractTermLike, dict, syms)
    coef = MP.coefficient(term)
    mono = _to_term(reference, MP.monomial(term), dict, syms)
    if isone(coef)
        return mono
    else
        return MP.coefficient(term) * mono
    end
end

function _to_term(reference, x::MP.AbstractPolynomialLike, dict, syms)
    if MP.nterms(x) == 0
        return 0
    elseif MP.nterms(x) == 1
        return _to_term(reference, first(MP.terms(x)), dict, syms)
    else
        terms = map(MP.terms(x)) do term
            _to_term(reference, term, dict, syms)
        end
        return similarterm(reference, +, terms, symtype(reference))
    end
end

function _to_term(reference, x, dict, vars)
    if istree(x)
        t = similarterm(x, operation(x), _to_term.((reference,), arguments(x), (dict,), (vars,)), symtype(x))
    else
        if haskey(dict, x)
            return dict[x]
        else
            return x
        end
    end
end

<ₑ(a::MP.AbstractPolynomialLike, b::MP.AbstractPolynomialLike) = false

"""
    expand(expr, variable_type::Type=DynamicPolynomials.PolyVar{true})

Expand expressions by distributing multiplication over addition, e.g.,
`a*(b+c)` becomes `ab+ac`.

`expand` uses replace symbols and non-algebraic expressions by variables of type
`variable_type` to compute the distribution using a specialized sparse
multivariate polynomials implementation.
`variable_type` can be any subtype of `MultivariatePolynomials.AbstractVariable`.
"""
function expand(expr, variable_type::Type=DynamicPolynomials.PolyVar{true})
    to_term(expr, to_mpoly(expr, variable_type)...)
end

## Hack to fix https://github.com/JuliaAlgebra/MultivariatePolynomials.jl/issues/169

Base.promote_rule(::Type{S}, ::Type{T}) where {S<:Symbolic, T<:MP.AbstractPolynomialLike}= Any
Base.promote_rule(::Type{T}, ::Type{S}) where {S<:Symbolic, T<:MP.AbstractPolynomialLike}= Any

Base.@deprecate polynormalize(x) expand(x)
