using SymbolicUtils, Test
using SymbolicUtils: polynormalize
@testset "polyform" begin
    @syms a b c d
    @test polynormalize(a * (b + -1 * c) + -1 * (b * a + -1 * c * a)) == 0
    @eqtest polynormalize(sin((a+b)^2)^2) == sin(a^2+b^2+2*a*b)^2
    # fixme: can this be made faster?
    @test simplify(polynormalize(sin((a+b)^2)^2 + cos((a+b)^2)^2)) == 1
end
