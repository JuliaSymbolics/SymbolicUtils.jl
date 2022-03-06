using SymbolicUtils
using SymbolicUtils: <ₑ, sort_args
using Metatheory

# TODO symbolic equality is extremely broken

sym_eq(x, y) = simplify(x == y)

@testset "Basic optimization" begin
    @syms a b c x y z
    ex = 2a + 2b - (a * (a + b))
    res = optimize(ex)
    @show res
    @test repr(res) == "(b + a)*(2 - a)"

    ex = sin(a^2) / cos(a^2)
    res = optimize(ex)
    @test repr(res) == "tan(a^2)" # sym_eq does not work
    # TODO report issue

    ex = sin(1 / x * (a * b + a * c))^2 + cos((a * (b + c)) / x)^2
    res = optimize(ex)
    @test res == 1
end


