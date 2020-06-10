"""
    labels(dict, t)

Find all terms that are not + and * and replace them
with a symbol, store the symbol => term mapping in `dict`.
"""
function labels end

# Turn a Term into a multivariate polynomial
labels(dicts, t; label_terms=false) = t
function labels(dicts, t::Sym; label_terms=false)
    sym2term, term2sym = dicts
    if !haskey(term2sym, t)
        sym2term[t] = t
        term2sym[t] = t
    end
    return t
end

function labels(dicts, t::Term; label_terms=false)
    tt = arguments(t)
    if operation(t) == (*) || operation(t) == (+)
        return Term{symtype(t)}(operation(t), map(x->labels(dicts, x;
                                                            label_terms=label_terms), tt))
    else
        sym2term, term2sym = dicts
        if haskey(term2sym, t)
            return term2sym[t]
        end
        if label_terms
            sym = Sym{symtype(t)}(gensym(nameof(operation(t))))
            sym2term[sym] = Term{symtype(t)}(operation(t), map(x->labels(dicts, x;
                                                                        label_terms=label_terms),
                                                               tt))
            x = term2sym[t] = sym

            return x
        else
            return Term{symtype(t)}(operation(t), map(x->labels(dicts, x; label_terms=label_terms), tt))
        end
    end
end

ismpoly(x) = x isa MPoly || x isa Integer

function to_mpoly(t)
    sym2term, term2sym = Dict(), Dict()
    ls = labels((sym2term, term2sym), t)

    if isempty(sym2term)
        return t, []
    end

    ks = collect(keys(sym2term))
    R, vars = PolynomialRing(ZZ, String.(nameof.(ks)))

    t_poly_1 = substitute(t, term2sym, fold=false)
    t_poly_2 = substitute(t_poly_1, Dict(ks .=> vars), fold=false)
    rs = RuleSet([@rule(~x::ismpoly - ~y::ismpoly => ~x + -1 * (~y))
                  @acrule(~x::ismpoly + ~y::ismpoly => ~x + ~y)
                  @rule(+(~x) => ~x)
                  @acrule(~x::ismpoly * ~y::ismpoly => ~x * ~y)
                  @rule(*(~x) => ~x)
                  @rule((~x::ismpoly)^(~a::isliteral(Integer)) => (~x)^(~a))])
    simplify(t_poly_2, EmptyCtx(), rules=rs), Dict(Pair.(1:length(vars), ks))
end

function to_term(x::MPoly, syms)
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
    if length(monoms) == 1
        !isone(x.coeffs[1]) ?  monoms[1] * x.coeffs[1] : monoms[1]
    elseif length(monoms) == 0
        return 0
    else
        Term(+, map((x,y)->isone(y) ? x : y*x, monoms, x.coeffs[1:length(monoms)]))
    end
end

to_term(x, vars) = x

function to_term(x::Term, vars)
    Term{symtype(x)}(operation(x), to_term.(arguments(x), (vars,)))
end

<ₑ(a::MPoly, b::MPoly) = false
