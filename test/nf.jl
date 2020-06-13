using SymbolicUtils, Test
using SymbolicUtils: polynormalize
@testset "polyform" begin
    @syms a b c d
    @test polynormalize(a * (b + -1 * c) + -1 * (b * a + -1 * c * a)) == 0
    @eqtest simplify(polynormalize(sin((a+b)^2)^2)) == simplify(sin(a^2+2*(b*a)+b^2)^2)
    @test simplify(polynormalize(sin((a+b)^2)^2 + cos((a+b)^2)^2)) == 1
end
