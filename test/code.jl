using Test, SymbolicUtils
using SymbolicUtils.Code
@testset "toexpr level 1" begin
    @syms a b c d e t x(t) y(t) z(t)
    @test toexpr(Assignment(a, b)) == :(a = b)
    @test toexpr(a+b) == :($(+)(a, b))
    @test toexpr(a+b) == :($(+)(a, b))
    @test toexpr(x(t)+y(t)) == :($(+)(var"x(t)", var"y(t)"))
    @test toexpr(x(t)+y(t)+x(t+1)) == :($(+)(var"x(t)", var"y(t)", var"x(1 + t)"))
end
