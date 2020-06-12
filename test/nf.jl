using SymbolicUtils, Test
@testset "polyform" begin
    @syms a b c d
    @test simplify(a * (b + -1 * c) + -1 * (b * a + -1 * c * a), mpoly=true) == 0
    @eqtest simplify(sin((a+b)^2)^2; mpoly=true) == sin(a^2+b^2+2*a*b)^2
    # fixme: can this be made faster?
    @test simplify(sin((a+b)^2)^2 + cos((a+b)^2)^2; mpoly=true) == 1
end
