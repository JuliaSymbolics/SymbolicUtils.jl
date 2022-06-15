using SymbolicUtils
using Metatheory

sym_eq(x, y) = simplify(x == y)

@testset "Basic optimization" begin
    @syms a b c x y z
    ex = 2a + 2b - (a*(a + b))
    res = optimize(ex)
    @test_broken sym_eq(res, (a+b)*(2-a))

    ex = sin(a^2)/cos(a^2)
    res = optimize(ex)
    @test_broken isequal(res, tan(a^2)) # sym_eq does not work
    # TODO report issue

    ex = sin(1/x * (a * b + a * c))^2 + cos((a*(b+c))/x)^2
    res = optimize(ex)
    @test_broken res == 1
end
