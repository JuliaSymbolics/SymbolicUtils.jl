using SymbolicUtils, Test
using SymbolicUtils: polynormalize, Term, symtype
@testset "polyform" begin
    @syms a b c d
    @test polynormalize(a * (b + -1 * c) + -1 * (b * a + -1 * c * a)) == 0
    @eqtest polynormalize(sin(a+b)+sin(c+d)) == sin(a+b) + sin(c+d)
    @eqtest simplify(polynormalize(sin((a+b)^2)^2)) == simplify(sin(a^2+2*(b*a)+b^2)^2)
    @test simplify(polynormalize(sin((a+b)^2)^2 + cos((a+b)^2)^2)) == 1
    @syms x1::Real f(::Real)::Real

    # issue 193
    @test isequal(polynormalize(f(x1 + 2.0)), f(2.0 + x1))
    @test symtype(polynormalize(f(x1 + 2.0))) == Real

    # cleanup rules
    @test polynormalize(Term{Number}(identity, 0)) == 0
    @test polynormalize(Term{Number}(one, 0)) == 1
    @test polynormalize(Term{Number}(zero, 0)) == 0
    @test polynormalize(identity(a * b) - b * a) == 0
    @test polynormalize(a * b - b * a) == 0
end
