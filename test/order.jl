using Test
using Combinatorics
using SymbolicUtils: <ₑ, arguments
SymbolicUtils.show_simplified[] = false

@syms a b c

function istotal(x, y)
    #either
    if x <ₑ y
        return !(y <ₑ x)
    elseif y <ₑ x
        return !(x <ₑ y) # already tested
    else
        # neither, equal
        return isequal(x, y)
    end
end

@test istotal(a,a)
@test istotal(a,b)
@test istotal(2,a)
@test 2 <ₑ a
@test a <ₑ b
@test istotal(a, 2a)
@test a <ₑ 2a
@test istotal(b*a, a)
@test istotal(a, b*a)
@test !(b*a <ₑ b+a)
@test Term(^, [1,-1]) <ₑ a
@test istotal(a, Term(^, [1,-1]))

@testset "callable variable order" begin
    @syms z() ρ()

    @test istotal(ρ(), -1z())

    @syms a(t) b(t) t
    @test a(t) <ₑ b(t)
    @test !(b(t) <ₑ a(t))

    @syms y() x()
    @test x() <ₑ y()
    @test !(y() <ₑ x())
end

@testset "Sym vs Term" begin
    @syms x y

    @test x <ₑ (3 + x) && !((3 + x) <ₑ x)
    @test istotal(y, x^2)
end

@testset "small terms" begin
    # this failing was a cause of a nasty stackoverflow #82
    @syms a
    istotal(Term(^, [a, -1]), (a + 2))
end

@testset "transitivity" begin
    # issue #160
    @syms σ x y z
    expr = σ*sin(x + -1y)*(sin(z)^2)*(-1x + y)
    args = sort(arguments(expr), lt=<ₑ)
    @test all(((a, b), )->a <ₑ b,  combinations(args, 2))
end
