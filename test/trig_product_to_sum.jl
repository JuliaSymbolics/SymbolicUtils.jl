using Test
using SymbolicUtils

@testset "Trigonometric product-to-sum rules" begin
    @syms A B t ω φ ψ

    # Test basic product-to-sum identities
    @test isequal(simplify(cos(A) * cos(B)), (cos(A - B) + cos(A + B)) / 2)
    @test isequal(simplify(sin(A) * sin(B)), (cos(A - B) - cos(A + B)) / 2)
    @test isequal(simplify(sin(A) * cos(B)), (sin(A + B) + sin(A - B)) / 2)
    
    # Note: cos(A) * sin(B) produces sin(-A + B) instead of sin(B - A) due to ordering
    # but they are mathematically equivalent: sin(-A + B) = sin(B - A)
    result = simplify(cos(A) * sin(B))
    expected1 = (sin(A + B) - sin(A - B)) / 2
    expected2 = (sin(A + B) + sin(-A + B)) / 2
    @test isequal(result, expected1) || isequal(result, expected2)

    # Test with constants
    @test isequal(simplify(2 * cos(A) * cos(B)), (cos(A - B) + cos(A + B)))
    
    # Test issue #1644 scenario - energy systems
    expr = cos(ω*t + φ) * cos(ω*t + φ - ψ)
    simplified = simplify(expr)
    
    # The result should contain cos(ψ) and cos(2ω*t + 2φ - ψ) terms
    @test occursin("cos(ψ)", string(simplified)) || occursin("cos(-ψ)", string(simplified))
    @test occursin("cos(2", string(simplified))
    
    println("All trigonometric product-to-sum tests passed!")
end