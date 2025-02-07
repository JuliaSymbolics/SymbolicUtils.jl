using SymbolicUtils, SymbolicUtils.Code, Test
using SymbolicUtils.Code: topological_sort

@testset "CSE" begin
    @syms x
    t = cse(hypot(hypot(cos(x), sin(x)), atan(cos(x), sin(x))))

    @test t isa Let
    @test length(t.pairs) == 4
    @test occursin(t.pairs[3].lhs, t.body)
    @test occursin(t.pairs[4].lhs, t.body)
end

@testset "DAG CSE" begin
    @syms a b
    expr = sin(a + b) * (a + b)
    sorted_nodes = topological_sort(expr)
    @test length(sorted_nodes) == 3
    @test isequal(sorted_nodes[1].rhs, term(+, a, b))
    @test isequal(sin(sorted_nodes[1].lhs), sorted_nodes[2].rhs)

    expr = (a + b)^(a + b)
    sorted_nodes = topological_sort(expr)
    @test length(sorted_nodes) == 2
    @test isequal(sorted_nodes[1].rhs, term(+, a, b))
    ab_node = sorted_nodes[1].lhs
    @test isequal(term(^, ab_node, ab_node), sorted_nodes[2].rhs)
    let_expr = cse(expr)
    @test length(let_expr.pairs) == 1
    @test isequal(let_expr.pairs[1].rhs, term(+, a, b))
    corresponding_sym = let_expr.pairs[1].lhs
    @test isequal(let_expr.body, term(^, corresponding_sym, corresponding_sym))

    expr = a + b
    sorted_nodes = topological_sort(expr)
    @test length(sorted_nodes) == 1
    @test isequal(sorted_nodes[1].rhs, term(+, a, b))
    let_expr = cse(expr)
    @test isempty(let_expr.pairs)
    @test isequal(let_expr.body, term(+, a, b))
    
    expr = a
    sorted_nodes = topological_sort(expr)
    @test isempty(sorted_nodes)
    let_expr = cse(expr)
    @test isempty(let_expr.pairs)
    @test isequal(let_expr.body, a)

    # array symbolics
    # https://github.com/JuliaSymbolics/SymbolicUtils.jl/pull/688#pullrequestreview-2554931739
    @syms c
    function foo end
    ex = term(foo, [a^2 + b^2, b^2 + c], c; type = Real)
    sorted_nodes = topological_sort(ex)
    @test length(sorted_nodes) == 6
end
