using SymbolicUtils, SymbolicUtils.Code, Test
@testset "CSE" begin
    @syms x
    t = cse(hypot(hypot(cos(x), sin(x)), atan(cos(x), sin(x))))

    @test t isa Let
    @test length(t.pairs) == 2
    @test occursin(t.pairs[1].lhs, t.body)
    @test occursin(t.pairs[2].lhs, t.body)
end
