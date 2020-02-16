

@testset "Trig" begin
    @vars a::Integer x::Real y::Number
    r = rewriter(SymbolicUtils.TRIG_RULES)

    @test r(cos(x)^2 + 1 + sin(x)^2) == 2
    @test r(cos(y)^2 + 1 + sin(y)^2) == 2

    @test r(sin(y)^2 + cos(y)^2 + 1) == 2

    @test r(cos(x + 2π + a)) == cos(x + a)
    @test r(tan(x + 2π * a)) == tan(x)
    
end
