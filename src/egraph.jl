using Metatheory.Rewriters

function EGraphs.preprocess(t::Symbolic)
    toterm(unflatten(t))
end

function symbolicegraph(ex)
    g = EGraph(ex)
    analyze!(g, SymbolicUtils.SymtypeAnalysis)
    settermtype!(g, Term{symtype(ex)})
    return g
end


"""
Equational rewrite rules for optimizing expressions
"""
opt_theory = @theory a b x y  begin
    a + b == b + a
    a * b == b * a
    a * x + a * y == a*(x+y)
    -1 * a == -a
    a + (-1 * b) == a - b
    x^-1 == 1/x
    1/x * a == a/x
    # fraction rules
    # (a/b) + (c/b) => (a+c)/b
    # trig functions
    sin(x)/cos(x) == tan(x)
    cos(x)/sin(x) == cot(x)
    sin(x)^2 + cos(x)^2 --> 1
    sin(2a) == 2sin(a)cos(a)
end


"""
Approximation of costs of operators in number
of CPU cycles required for the numerical computation

See
 * https://latkin.org/blog/2014/11/09/a-simple-benchmark-of-various-math-operations/
 * https://streamhpc.com/blog/2012-07-16/how-expensive-is-an-operation-on-a-cpu/
 * https://github.com/triscale-innov/GFlops.jl
"""
const op_costs = Dict(
    (+)     => 1,
    (-)     => 1,
    abs     => 2,
    (*)     => 3,
    exp     => 18,
    (/)     => 24,
    (^)     => 100,
    log1p   => 124,
    deg2rad => 125,
    rad2deg => 125,
    acos    => 127,
    asind   => 128,
    acsch   => 133,
    sin     => 134,
    cos     => 134,
    atan    => 135,
    tan     => 156,
)
# TODO some operator costs are in FLOP and not in cycles!!

function costfun(n::ENodeTerm, g::EGraph, an)
    op = operation(n)
    cost = 0
    cost += get(op_costs, op, 1)

    for id ∈ n.args
        eclass = g[id]
        !hasdata(eclass, an) && (cost += Inf; break)
        cost += last(getdata(eclass, an))
    end
    cost
end

costfun(n::ENodeLiteral, g::EGraph, an) = 0

egraph_simterm(x, head, args, symtype=nothing; metadata=nothing, exprhead=exprhead(x)) =
    TermInterface.similarterm(typeof(x), head, args, symtype; metadata=metadata, exprhead=exprhead)

# Custom similarterm to use in EGraphs on <:Symbolic types that treats everything as a Term
function egraph_simterm(x::Type{<:BasicSymbolic}, f, args, symtype=nothing; metadata=nothing, exprhead=:call)
    T = symtype
    if T === nothing
        T = _promote_symtype(f, args)
    end
    res = Term{T}(f isa Symbol ? eval(f) : f, args; metadata=metadata)
    return res
end

function optimize(ex; params=SaturationParams(timeout=20))
    # @show ex
    g = symbolicegraph(ex)
    params.simterm = egraph_simterm
    saturate!(g, opt_theory, params)
    return extract!(g, costfun)
end
