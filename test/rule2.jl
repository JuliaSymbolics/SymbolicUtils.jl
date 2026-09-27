

function int_and_subst(expr::SymsType, var::SymsType, old::SymsType, new::SymsType, tag::String)::SymsType
    print("int_and_subst called with expr: "); show(expr); println()
    print(" var: "); show(var); println()
    print(" old: "); show(old); println()
    print(" new: "); show(new); println()
    print(" tag: "); show(tag); println()
    return expr #dummy
end


function generate_random_expression_r(depth::Int, syms::Vector{SymsType}, operations::Vector{Symbol})::SymsType
    if depth == 0
        return syms[rand(1:length(syms))]
    end
    op = operations[rand(1:length(operations))]
    if op in [:+, :-, :*, :/, :^]
        left = generate_random_expression_r(depth - 1, syms, operations)
        right = generate_random_expression_r(depth - 1, syms, operations)
        return eval(op)(left, right)
    elseif op in [:log, :sin, :cos, :exp]
        arg = generate_random_expression_r(depth - 1, syms, operations)
        return eval(op)(arg)
    elseif op == :∫
        var = syms[rand(1:length(syms))]
        integrand = generate_random_expression_r(depth - 1, syms, operations)
        return ∫(integrand, var)
    else
        error("Unknown operation: $op")
    end
end

function generate_random_expression()
    operations = [:+, :-, :*, :/, :^, :log, :sin, :cos, :exp, :∫]
    syms = [a, b, c, d, e, f, g, h]
    return generate_random_expression_r(3, syms, operations)
end

# function generate_random_rule_r2(depth::Int, syms::Vector{SymsType}, operations::Vector{Symbol})::Expr
#     if depth == 0
#         choosen = syms[rand(1:length(syms))]
#         return :(~($choosen))
#     end
#     op = operations[rand(1:length(operations))]
#     if op in [:+, :-, :*, :/, :^]
#         left = generate_random_rule_r2(depth - 1, syms, operations)
#         right = generate_random_rule_r2(depth - 1, syms, operations)
#         return Expr(:call, op, left, right)
#     elseif op in [:log, :sin, :cos, :exp]
#         arg = generate_random_rule_r(depth - 1, syms, operations)
#         return Expr(:call, op, arg)
#     elseif op == :∫
#         var = syms[rand(1:length(syms))]
#         integrand = generate_random_rule_r2(depth - 1, syms, operations)
#         return Expr(:call, :∫, integrand, Expr(:call, :~, var))
#     else
#         error("Unknown operation: $op")
#     end
# end
# 
# function generate_random_rule2()
#     operations = [:+, :-, :*, :/, :^, :log, :sin, :cos, :exp, :∫]
#     syms = [a, b, c, d, e, f, g, h]
#     lhs = generate_random_rule_r2(3, syms, operations)
#     rhs = generate_random_rule_r2(3, syms, operations)
#     return (lhs, rhs)
# end
# 
# function generate_random_rule1()
#     operations = [:+, :-, :*, :/, :^, :log, :sin, :cos, :exp, :∫]
#     syms = [a, b, c, d, e, f, g, h]
#     lhs = generate_random_rule_r2(3, syms, operations)
#     rhs = generate_random_rule_r2(3, syms, operations)
#     r = @rule lhs => rhs
#     println("Generated random rule: "); show(r); println(typeof(r))
#     return r
# end

function testrule1(n::Int, verbose::Bool=false)
    @syms x ∫(var1, var2) a b c d e f g h
    rules = SymbolicUtils.Rule[]
    for i in 1:n
        r = @rule ∫(((~f) + (~!g)*(~x))^(~!q)*((~!a) + (~!b)*log((~!c)*((~d) + (~!e)*(~x))^(~!n)))^(~!p),(~x)) =>
        1⨸(~e)*int_and_subst(((~f)*(~x)⨸(~d))^(~q)*((~a) + (~b)*log((~c)*(~x)^(~n)))^(~p),  (~x), (~x), (~d) + (~e)*(~x), "3_3_2")
        push!(rules, r)
    end

    # set random seed for reproducibility
    Random.seed!(1234)
    for i in 1:n
        rex = generate_random_expression()
        verbose && print("$i) checking against expression: ", rex)
        result = rules[i](rex)
        if result === nothing
            verbose && println(" NO MATCH")
        else
            verbose && println(" YES MATCH: ", result)
        end
    end
end


function testrule2(n::Int, verbose::Bool=false)
    @syms x ∫(var1, var2) a b c d e f g h
    rules = Pair{Expr, Expr}[]
    for i in 1:n
        r = (:(∫(((~f) + (~!g)*(~x))^(~!q)*((~!a) + (~!b)*log((~!c)*((~d) + (~!e)*(~x))^(~!n)))^(~!p),(~x))) =>
        :(1⨸(~e)*int_and_subst(((~f)*(~x)⨸(~d))^(~q)*((~a) + (~b)*log((~c)*(~x)^(~n)))^(~p),  (~x), (~x), (~d) + (~e)*(~x), "3_3_2")))
        push!(rules, r)
    end

    # set random seed for reproducibility
    Random.seed!(1234)
    for i in 1:n
        rex = generate_random_expression()
        verbose && print("$i) checking against expression: ", rex)
        result = SymbolicUtils.rule2(rules[i], rex)
        if result === nothing
            verbose && println(" NO MATCH")
        else
            verbose && println(" YES MATCH: ", result)
        end
    end
end



""" Results on macbook air m1:
julia> @benchmark testrule2(\$1000)
BenchmarkTools.Trial: 244 samples with 1 evaluation per sample.
 Range (min … max):  18.481 ms … 29.089 ms  ┊ GC (min … max): 0.00% … 30.02%
 Time  (median):     19.456 ms              ┊ GC (median):    0.00%
 Time  (mean ± σ):   20.564 ms ±  2.652 ms  ┊ GC (mean ± σ):  6.09% ± 10.54%

     ▄▆█▇▄▁                                                    
  ▇█▇██████▁▄▆▆▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▄▆▆▄▁▆▄▁▄▁▁▄▄▁▄▆▆▄▄▁▇▆▇▆▄▇▆▁▆▄ ▆
  18.5 ms      Histogram: log(frequency) by time      28.2 ms <

 Memory estimate: 13.07 MiB, allocs estimate: 356839.

julia> @benchmark testrule1(\$1000)
BenchmarkTools.Trial: 11 samples with 1 evaluation per sample.
 Range (min … max):  446.396 ms … 472.119 ms  ┊ GC (min … max): 0.00% … 5.67%
 Time  (median):     461.125 ms               ┊ GC (median):    3.27%
 Time  (mean ± σ):   460.506 ms ±   7.303 ms  ┊ GC (mean ± σ):  3.12% ± 1.73%

  ▁      ▁                     █    █ ▁  ▁   ▁      ▁         ▁  
  █▁▁▁▁▁▁█▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁█▁▁▁▁█▁█▁▁█▁▁▁█▁▁▁▁▁▁█▁▁▁▁▁▁▁▁▁█ ▁
  446 ms           Histogram: frequency by time          472 ms <

 Memory estimate: 110.40 MiB, allocs estimate: 3393493.
"""

function testpredicates()
    @syms ∫ a
    SymbolicUtils.rule2(:(∫(1 / (~x)^(~m::iseven), ~x)) => :(log(~x)*~m), ∫(1/a^3,a))===nothing
    SymbolicUtils.rule2(:(∫(1 / (~x)^(~m::iseven), ~x)) => :(log(~x)*~m), ∫(1/a^2,a))!==nothing
end