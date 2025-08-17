using Metatheory
using SymbolicUtils 
const SU = SymbolicUtils
using SymbolicUtils: Symbolic, BasicSymbolic, unflatten, toterm, Term
using SymbolicUtils: monadic, diadic
using InteractiveUtils

EGraphs.preprocess(t::Symbolic) = toterm(unflatten(t)) 

"""
Equational rewrite rules for optimizing expressions
"""
opt_theory = @theory a b c x y z begin
    a + (b + c) == (a + b) + c
    a * (b * c) == (a * b) * c
    x + 0 --> x
    a + b == b + a
    a - a => 0 # is it ok?

    0 - x --> -x

    a * b == b * a
    a * x + a * y == a*(x+y)
    -1 * a --> -a
    a + (-1 * b) == a - b
    x * 1 --> x
    x * 0 --> 0
    x/x --> 1
    # fraction rules 
    x^-1 == 1/x 
    1/x * a == a/x # is this needed?
    x / (x / y) --> y
    x * (y / z) == (x * y) / z
    (a/b) + (c/b) --> (a+c)/b
    (a / b) / c == a/(b*c)
    
    # TODO prohibited rule 
    x / x --> 1

    # pow rules 
    a * a == a^2
    (a^b)^c == a^(b*c)
    a^b * a^c == a^(b+c)
    a^b / a^c == a^(b-c)
    (a*b)^c == a^c * b^c

    # logarithmic rules 
    # TODO variables are non-zero
    log(x::Number) => log(x)
    log(x * y) == log(x) + log(y)
    log(x / y) == log(x) - log(y)
    log(x^y) == y * log(x)
    x^(log(y)) == y^(log(x))

    # trig functions
    sin(x)/cos(x) == tan(x)
    cos(x)/sin(x) == cot(x)
    sin(x)^2 + cos(x)^2 --> 1
    sin(2a) == 2sin(a)cos(a)

    sin(x)*cos(y) - cos(x)*sin(y) --> sin(x - y) 
    # hyperbolic trigonometric 
    # are these optimizing at all? dont think so
    sinh(x) == (ℯ^x - ℯ^(-x))/2
    csch(x) == 1/sinh(x) 
    cosh(x) == (ℯ^x + ℯ^(-x))/2
    sech(x) == 1/cosh(x) 
    sech(x) == 2/(ℯ^x + ℯ^(-x))
    tanh(x) == sinh(x)/cosh(x) 
    tanh(x) == (ℯ^x - ℯ^(-x))/(ℯ^x + ℯ^(-x))
    coth(x) == 1/tanh(x) 
    coth(x) == (ℯ^x + ℯ^-x)/(ℯ^x - ℯ^(-x)) 

    cosh(x)^2 - sinh(x)^2 --> 1
    tanh(x)^2 + sech(x)^2 --> 1
    coth(x)^2 - csch(x)^2 --> 1 

    asinh(z) == log(z + √(z^2 + 1))
    acosh(z) == log(z + √(z^2 - 1))    
    atanh(z) == log((1+z)/(1-z))/2
    acsch(z) == log((1+√(1+z^2)) / z )
    asech(z) == log((1 + √(1-z^2)) / z )
    acoth(z) == log( (z+1)/(z-1) )/2 

    # folding 
    x::Number * y::Number => x*y
    x::Number + y::Number => x+y
    x::Number / y::Number => x/y
    x::Number - y::Number => x-y
end


# See 
#  * https://latkin.org/blog/2014/11/09/a-simple-benchmark-of-various-math-operations/
#  * https://streamhpc.com/blog/2012-07-16/how-expensive-is-an-operation-on-a-cpu/
#  * https://github.com/triscale-innov/GFlops.jl
# Measure the cost of expressions in terms of number of ASM instructions 


function make_op_costs()
    const op_costs = Dict()
    
    const types = [(Int64, Integer), (Float64, Real), (ComplexF64, Complex)]
    
    const io = IOBuffer()
    
    for f in vcat(monadic, [-]) 
        z = get!(op_costs, nameof(f), Dict())
        for (t, at) in types
            try 
                InteractiveUtils.code_native(io, f, (t,))
            catch e
                z[(t,)] = z[(at,)] = 1
                continue 
            end
            str = String(take!(io))
            z[(t,)] = z[(at,)] = length(split(str, "\n"))
        end
    end
    
    for f in vcat(diadic, [+, -, *, /, //, ^])
        z = get!(op_costs, nameof(f), Dict())
        for (t1, at1) in types, (t2, at2) in types
            try 
                InteractiveUtils.code_native(io, f, (t1, t2))
            catch e
                z[(t1, t2)] = z[(at1, at2)] = z[(at1, t2)] = z[(t1, at2)] = 1
                continue 
            end
            str = String(take!(io))
            z[(t1, t2)] = z[(at1, at2)] = z[(at1, t2)] = z[(t1, at2)] =  length(split(str, "\n"))
        end
    end

    op_costs
end

function getopcost(op_costs, f::Function, types::Tuple)
    sym = nameof(f)
    if haskey(op_costs, sym) && haskey(op_costs[sym], types)
        return op_costs[sym][types]
    end

    # print("$f $types | ")
    io = IOBuffer()
    try 
        InteractiveUtils.code_native(io, f, types)
    catch e
        op_costs[sym][types] = 1
        return 1 
    end
    str = String(take!(io))
    c = length(split(str, "\n"))
    !haskey(op_costs, sym) && (op_costs[sym] = Dict())
    op_costs[sym][types] = c
end

getopcost(f, types::Tuple) = get(get(op_costs, f, Dict()), types, 1) 

function costfun(n::VecExpr, op, children_costs::Vector{Float64})    
    v_isexpr(n) || return 1
    # types = Tuple(map(x -> getdata(g[x], SymtypeAnalysis, Real), args))
    types = Tuple([Float64 for i in 1:v_arity(n)])
    opc = getopcost(op, types)
    opc + sum(children_costs)
end

denoisescalars(x, atol=1e-11) = Postwalk(Chain([
    # 0 - x --> -x
    @acrule *(~x::Real, sin(~y)) => 0 where isapprox(x, 0; atol=atol)
    @acrule *(~x::Real, cos(~y)) => 0 where isapprox(x, 0; atol=atol)
    @acrule +(~x::Real, ~y) => y where isapprox(x, 0; atol=atol)
    @acrule +(~x::Real, ~y) => y where isapprox(x, 0; atol=atol)
]))(x)

const op_costs = make_op_costs()
function optimize(ex::Symbolic; params=SaturationParams(), atol=1e-13, verbose=false, kws...)
    # ex = simplify(denoisescalars(ex, atol))
    # println(ex)
    # readline()

    g = EGraph{BasicSymbolic}(ex)

    # display(g.classes);println();

    report = saturate!(g, opt_theory, params)
    verbose && @info report
    extr = extract!(g, costfun)
    return extr
end

@syms x y z

t = Term(+, [Term(*, [z, x]), Term(*, [z, y])])

optimize(t)