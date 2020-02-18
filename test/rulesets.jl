@testset "Numeric" begin
    @vars a::Integer b c d x::Real y::Number 
    @test simplify(x - y) == x + -1*y
    @test simplify(1 * x * 2) == 2 * x
    @test simplify(1 + x + 2) == 3 + x
    
    @test simplify(a + b + (x * y) + c + 2 * (x * y) + d)     == (3 * x * y) + a + b + c + d
    @test simplify(a + b + 2 * (x * y) + c + 2 * (x * y) + d) == (4 * x * y) + a + b + c + d

    @test simplify(a * x^y * b * x^d) == (x^(y+d) * a * b)

    @test simplify(a + b + 0*c + d) == a + b + d
    @test simplify(a * b * c^0 * d) == a * b * d
    @test simplify(a * b * 1*c * d) == a * b * c * d
end

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
