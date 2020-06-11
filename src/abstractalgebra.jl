using DataStructures

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
    if t isa Term && (operation(t) == (*) || operation(t) == (+) || operation(t) == (-))
        tt = arguments(t)
        return Term{symtype(t)}(operation(t), map(x->labels!(dicts, x), tt))
    elseif t isa Integer
        return t
    else
        sym2term, term2sym = dicts
        if haskey(term2sym, t)
            return term2sym[t]
        end
        if t isa Term
            tt = arguments(t)
            sym = Sym{symtype(t)}(gensym(nameof(operation(t))))
            sym2term[sym] = Term{symtype(t)}(operation(t),
                                             map(x->to_mpoly(x, dicts)[1], tt))
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

function to_mpoly(t, dicts=(OrderedDict(), OrderedDict()))
    # term2sym is only used to assign the same
    # symbol for the same term -- in other words,
    # it does common subexpression elimination

    sym2term, term2sym = dicts
    labeled = labels!((sym2term, term2sym), t)

    if isempty(sym2term)
        return labeled, []
    end

    ks = collect(keys(sym2term))
    R, vars = PolynomialRing(ZZ, String.(nameof.(ks)))

    t_poly = substitute(labeled, Dict(ks .=> vars), fold=false)
    rs = RuleSet([@rule(~x::ismpoly - ~y::ismpoly => ~x + -1 * (~y))
                  @acrule(~x::ismpoly + ~y::ismpoly => ~x + ~y)
                  @rule(+(~x) => ~x)
                  @acrule(~x::ismpoly * ~y::ismpoly => ~x * ~y)
                  @rule(*(~x) => ~x)
                  @rule((~x::ismpoly)^(~a::isnonnegint) => (~x)^(~a))])
    simplify(t_poly, EmptyCtx(), rules=rs), sym2term, Dict(Pair.(1:length(vars), ks))
end

function to_term(x::MPoly, dict, syms)
    dict = copy(dict)
    for (k, v) in dict
        dict[k] = _to_term(v, dict, syms)
    end
    _to_term(x, dict, syms)
end

function _to_term(x::MPoly, dict, syms)

    function mul_coeffs(exps)
        monics = [e == 1 ? syms[i] : syms[i]^e for (i, e) in enumerate(exps) if !iszero(e)]
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

_to_term(x, dict, vars) = x

function _to_term(x::Term, dict, vars)
    t=Term{symtype(x)}(operation(x), _to_term.(arguments(x), (dict,), (vars,)))
end

<ₑ(a::MPoly, b::MPoly) = false
