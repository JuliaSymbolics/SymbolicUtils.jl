using Test
using SymbolicUtils
using SymbolicUtils: <ₑ

macro testord(expr)
    @assert expr.head == :call && expr.args[1] == :(<ₑ)

    x, y = expr.args[2:end]

    :(@test   $(esc(x)) <ₑ $(esc(y));
      @test !($(esc(y)) <ₑ $(esc(x))))
end

@testset "term order" begin
    @syms a b c x y z

    @testord -1 <ₑ 1
    @testord a <ₑ x
    @testord x <ₑ x^2
    @testord 2*x <ₑ x^2
    @testord 4*x^2 <ₑ x^3
    @testord 2*x^2 <ₑ 3*x^3

    @testord x <ₑ sin(x)
    @testord sin(x) <ₑ x^2
    @testord sin(x) <ₑ sin(x)^2
    @testord sin(x) <ₑ x*sin(x)
    @testord x*sin(x) <ₑ x^2*sin(x)
end
