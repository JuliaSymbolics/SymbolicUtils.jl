@testset "Pythagorean Identities" begin
    @vars a::Integer x::Real y::Number
    
    @test simplify(cos(x)^2 + 1 + sin(x)^2) == 2
    @test simplify(cos(y)^2 + 1 + sin(y)^2) == 2
    @test simplify(sin(y)^2 + cos(y)^2 + 1) == 2

    @test simplify(1 + y + tan(x)^2) == sec(x)^2 + y
    @test simplify(1 + y + cot(x)^2) == csc(x)^2 + y
end

@testset "2π  Identities" begin
    @vars a::Integer x::Real y::Number
   
    @test simplify(cos(x + 2π + a)) == cos(a + x)
    @test simplify(tan(x + 2π * a)) == tan(x)

end
