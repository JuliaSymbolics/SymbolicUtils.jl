# Polynomial Normal Form

"""
    labels!(dict, t)

Find all terms that are not + and * and replace them
with a symbol, store the symbol => term mapping in `dict`.
"""
function labels! end

# Turn a Term into a multivariate polynomial
function labels!(dicts, t::Sym)
    sym2term, term2sym = dicts
    if !haskey(term2sym, t)
        sym2term[t] = t
        term2sym[t] = t
    end
    return t
end

function labels!(dicts, t)
    if t isa Integer
        return t
    elseif t isa Term && (operation(t) == (*) || operation(t) == (+) || operation(t) == (-))
        tt = arguments(t)
        return Term{symtype(t)}(operation(t), map(x->labels!(dicts, x), arguments(t)))
    elseif t isa Term && operation(t) == (^) && length(arguments(t)) > 1 && isnonnegint(arguments(t)[2])
        return Term{symtype(t)}(operation(t), map(x->labels!(dicts, x), arguments(t)))
    else
        sym2term, term2sym = dicts
        if haskey(term2sym, t)
            return term2sym[t]
        end
        if t isa Term
            tt = arguments(t)
            sym = Sym{symtype(t)}(gensym(nameof(operation(t))))
            sym2term[sym] = Term{symtype(t)}(operation(t),
                                             map(x->to_mpoly(x, dicts)[1], arguments(t)))
        else
            sym = Sym{symtype(t)}(gensym("literal"))
            sym2term[sym] = t
        end

        term2sym[t] = sym

        return sym
    end
end

ismpoly(x) = x isa MPoly || x isa Integer
isnonnegint(x) = x isa Integer && x >= 0

let
    mpoly_rules = [@rule(~x::ismpoly - ~y::ismpoly => ~x + -1 * (~y))
                   @acrule(~x::ismpoly + ~y::ismpoly => ~x + ~y)
                   @rule(+(~x) => ~x)
                   @acrule(~x::ismpoly * ~y::ismpoly => ~x * ~y)
                   @rule(*(~x) => ~x)
                   @rule((~x::ismpoly)^(~a::isnonnegint) => (~x)^(~a))]

    global to_mpoly
    function to_mpoly(t, dicts=(OrderedDict{Sym, Any}(), OrderedDict{Any, Sym}()))
        # term2sym is only used to assign the same
        # symbol for the same term -- in other words,
        # it does common subexpression elimination

        sym2term, term2sym = dicts
        labeled = labels!((sym2term, term2sym), t)

        if isempty(sym2term)
            return labeled, []
        end

        ks = sort(collect(keys(sym2term)), lt=<ₑ)
        R, vars = PolynomialRing(ZZ, String.(nameof.(ks)))

        replace_with_poly = Dict{Sym,MPoly}(zip(ks, vars))
        t_poly = substitute(labeled, replace_with_poly, fold=false)
        Fixpoint(Postwalk(RestartedChain(mpoly_rules)))(t_poly), sym2term, ks
    end
end

function to_term(x, dict, syms)
    dict = copy(dict)
    for (k, v) in dict
        dict[k] = _to_term(v, dict, syms)
    end
    _to_term(x, dict, syms)
end

function _to_term(x::MPoly, dict, syms)

    function mul_coeffs(exps)
        monics = [e == 1 ? syms[i] : syms[i]^e for (i, e) in enumerate(reverse(exps)) if !iszero(e)]
        if length(monics) == 1
            return monics[1]
        elseif length(monics) == 0
            return 1
        else
            return Term(*, monics)
        end
    end

    monoms = [mul_coeffs(exponent_vector(x, i)) for i in 1:x.length]
    if length(monoms) == 0
        return 0
    end
    if length(monoms) == 1
        t = !isone(x.coeffs[1]) ?  monoms[1] * x.coeffs[1] : monoms[1]
    else
        t = Term(+, map((x,y)->isone(y) ? x : y*x, monoms, x.coeffs[1:length(monoms)]))
    end

    substitute(t, dict, fold=false)
end

function _to_term(x, dict, vars)
    if haskey(dict, x)
        return dict[x]
    else
        return x
    end
end

function _to_term(x::Term, dict, vars)
    t=Term{symtype(x)}(operation(x), _to_term.(arguments(x), (dict,), (vars,)))
end

<ₑ(a::MPoly, b::MPoly) = false
