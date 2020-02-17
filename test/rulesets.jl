@testset "Trig" begin
    @vars a::Integer x::Real y::Number
    
    @test simplify(cos(x)^2 + 1 + sin(x)^2) == 2
    @test simplify(cos(y)^2 + 1 + sin(y)^2) == 2

    @test simplify(sin(y)^2 + cos(y)^2 + 1) == 2

    @test simplify(cos(x + 2π + a)) == cos(a + x)
    @test simplify(tan(x + 2π * a)) == tan(x)
end
