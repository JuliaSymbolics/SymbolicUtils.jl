using Test
using SymbolicUtils

@testset "Trigonometric product-to-sum rules" begin
    @syms A B t ω φ ψ

    # Test that product-to-sum IS applied by default now
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
    
    # Test that trigexpand=false disables the transformation
    @test isequal(simplify(cos(A) * cos(B), trigexpand=false), cos(A) * cos(B))
    
    # Test issue #1644 scenario - energy systems
    expr = cos(ω*t + φ) * cos(ω*t + φ - ψ)
    
    # Default behavior now applies trigexpand
    expanded = simplify(expr)
    @test occursin("cos(ψ)", string(expanded)) || occursin("cos(-ψ)", string(expanded))
    @test occursin("cos(2", string(expanded))
    
    # With trigexpand=false - should remain unchanged
    unchanged = simplify(expr, trigexpand=false)
    @test isequal(unchanged, expr)
    
    # Test that trigexpand() function still works
    trigexpand_result = trigexpand(expr)
    @test isequal(expanded, trigexpand_result)
    
    println("All trigonometric product-to-sum tests passed!")
end