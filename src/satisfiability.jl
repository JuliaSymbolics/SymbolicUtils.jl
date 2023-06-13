import Z3

function check_z3(expr, syms)
    @assert symtype(expr) == Bool
    ctx = Z3.Context()

    @assert all(x->symtype(x) <: Real, syms)

    mapping = Dict(sym => Z3.real_const(ctx, string(sym)) for sym in syms)
    expr′ = substitute(expr, mapping, fold=true)

    @assert expr′ isa Z3.ExprAllocated

    opt = Z3.Optimize(ctx)
    Z3.add(opt, expr′)
    mapping, opt
end

function satisfiable(expr, syms)
    _, opt = check_z3(expr, syms)
    return Z3.check(opt) == Z3.sat
end

function satisfying_assignment(expr, syms)
    mapping, opt = check_z3(expr, syms)
    if Z3.check(opt) != Z3.sat
        error("expression is not satisfiable")
    end
    invmap = Dict(string(v) => k for (k, v) in mapping)
    [invmap[string(k)] => v for (k, v) in Z3.consts(Z3.get_model(opt))]
end
