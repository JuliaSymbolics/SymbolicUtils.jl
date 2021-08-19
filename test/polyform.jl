using SymbolicUtils: PolyForm
using Test, SymbolicUtils

@testset "div and polyform" begin
    @syms x y z
    @test repr(PolyForm(x-y)) == "x - y"
    @test repr(x/y*x/z) == "(x^2) / (y*z)"
    @test repr(simplify_fractions(((x-y+z)*(x+4z+1)) /
                                  (y*(2x - 3y + 3z) +
                                   x*(x + z)))) == "(x + 4z + 1) / (x + 3.0y)"
    @test simplify_fractions(x/(x+3) + 3/(x+3)) == 1
    @test simplify_fractions(cos(x)/sin(x) + sin(x)/cos(x))
end
