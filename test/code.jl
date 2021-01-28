using Test, SymbolicUtils
using SymbolicUtils.Code
using SymbolicUtils.Code: LazyState
@testset "toexpr level 1" begin
    @syms a b c d e t x(t) y(t) z(t)
    @test toexpr(Assignment(a, b)) == :(a = b)
    @test toexpr(a+b) == :($(+)(a, b))
    @test toexpr(a+b) == :($(+)(a, b))
    @test toexpr(a^b) == :($(^)(a, b))
    @test toexpr(a^2) == :($(^)(a, 2))
    @test toexpr(a^-2) == :($(^)($(inv)(a), 2))
    @test toexpr(x(t)+y(t)) == :($(+)(x(t), y(t)))
    @test toexpr(x(t)+y(t)+x(t+1)) == :($(+)(x(t), y(t), x($(+)(1, t))))
    s = LazyState()
    push!(s.symbolify, x(t))
    push!(s.symbolify, y(t))
    @test toexpr(x(t)+y(t)+x(t+1), s) == :($(+)(var"x(t)", var"y(t)", x($(+)(1, t))))
end
