using Metatheory, SymbolicUtils
using SymbolicUtils: Symbolic, BasicSymbolic, unflatten, toterm
using Metatheory: @rule

using SymbolicUtils: <ₑ

function EGraphs.preprocess(t::BasicSymbolic)
    toterm(unflatten(t))
end


"""
Equational rewrite rules for optimizing expressions
"""
opt_theory = @theory a b x y begin
    a + b == b + a
    a * b == b * a
    a * x + a * y == a * (x + y)
    -1 * a == -a
    a + (-1 * b) == a - b
    x^-1 == 1 / x
    1 / x * a == a / x
    # fraction rules
    # (a/b) + (c/b) => (a+c)/b
    # trig functions
    sin(x) / cos(x) == tan(x)
    cos(x) / sin(x) == cot(x)
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
    (+) => 1,
    (-) => 1,
    abs => 2,
    (*) => 3,
    exp => 18,
    (/) => 24,
    (^) => 100,
    log1p => 124,
    deg2rad => 125,
    rad2deg => 125,
    acos => 127,
    asind => 128,
    acsch => 133,
    sin => 134,
    cos => 134,
    atan => 135,
    tan => 156,
)
# TODO some operator costs are in FLOP and not in cycles!!

function costfun(n::VecExpr, op, children_costs::Vector{Float64})::Float64
    v_isexpr(n) || return 0 #1
    get(op_costs, op, 1) + sum(children_costs)
end


function optimize(ex; params=SaturationParams(timeout=20))
    # @show ex
    g = EGraph{BasicSymbolic}(ex)
    saturate!(g, opt_theory, params)
    return extract!(g, costfun)
end



# =======================================================================

@syms x y z a b c 

expr = ((a * b) + (a * c)) / ((x * y) + (x * z) )

g = EGraph{BasicSymbolic}(expr)
saturate!(g, opt_theory, SaturationParams())
return extract!(g, costfun)

@benchmark optimize(expr)