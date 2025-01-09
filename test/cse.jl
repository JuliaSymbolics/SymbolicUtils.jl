using SymbolicUtils, SymbolicUtils.Code, Test
using SymbolicUtils.Code: topological_sort

@testset "CSE" begin
    @syms x
    t = cse(hypot(hypot(cos(x), sin(x)), atan(cos(x), sin(x))))

    @test t isa Let
    @test length(t.pairs) == 2
    @test occursin(t.pairs[1].lhs, t.body)
    @test occursin(t.pairs[2].lhs, t.body)
end

@testset "DAG CSE" begin
    @syms a b
    expr = sin(a + b) * (a + b)
    sorted_nodes = topological_sort(expr)
    @test length(sorted_nodes) == 3
    expr = (a + b)^(a + b)
    sorted_nodes = topological_sort(expr)
    @test length(sorted_nodes) == 2
end
