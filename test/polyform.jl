using SymbolicUtils: PolyForm, Term, symtype
using Test, SymbolicUtils

@testset "div and polyform" begin
    @syms x y z
    @test repr(PolyForm(x-y)) == "x - y"
    @test repr(x/y*x/z) == "(x^2) / (y*z)"
    @test repr(simplify_fractions(((x-y+z)*(x+4z+1)) /
                                  (y*(2x - 3y + 3z) +
                                   x*(x + z)))) == "(x + 4z + 1) / (x + 3.0y)"
    @test simplify_fractions(x/(x+3) + 3/(x+3)) == 1
    @test repr(simplify(simplify_fractions(cos(x)/sin(x) + sin(x)/cos(x)))) == "1 / (cos(x)*sin(x))"
end

@testset "expand" begin
    @syms a b c d
    @test expand(a * (b + -1 * c) + -1 * (b * a + -1 * c * a)) == 0
    @eqtest simplify(expand(sin((a+b)^2)^2)) == simplify(sin(a^2+2*(b*a)+b^2)^2)
    @test simplify(expand(sin((a+b)^2)^2 + cos((a+b)^2)^2)) == 1
    @syms x1::Real f(::Real)::Real

    # issue 193
    #@test isequal(expand(f(2.0 + x1)), f(2.0 + x1))
    @test symtype(expand(f(x1 + 2.0))) == Real

    # cleanup rules
    # I don't think we need this anymore?
   #@test expand(Term{Number}(identity, 0)) == 0
   #@test expand(Term{Number}(one, 0)) == 1
   #@test expand(Term{Number}(zero, 0)) == 0
   #@test expand(identity(a * b) - b * a) == 0
    @test expand(a * b - b * a) == 0
end
