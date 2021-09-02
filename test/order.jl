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
@test a <ₑ Term(^, [1,-1])
@test istotal(a, Term(^, [1,-1]))

@testset "operator order" begin
    fs = (*, ^, /, \, -, +)
    for i in 1:length(fs)
        f = fs[i]
        @test f(a, b) <ₑ f(b, c)
        @test istotal(f(a, b), f(b, c))
        @test !(f(b, b) <ₑ f(b, b))
        @test istotal(f(b, b), f(b, b))
        @test !(f(b, c) <ₑ f(a, b))
        @test istotal(f(b, c), f(a, b))

        @test f(1, b) <ₑ f(2, b)
        @test !(f(2, b) <ₑ f(1, b))
        @test istotal(f(1, b), f(2, b))
        @test istotal(f(2, b), f(1, b))
        @test b <ₑ f(2,b) && !(f(2,b) <ₑ b)

        for j in i+1:length(fs)
            g = fs[j]
            @test istotal(f(a, b), g(a, b))
        end
    end
end

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
    expr = σ*sin(x + -1y)*(sin(z)^(-1))*(-1x + y)
    args = arguments(expr)
    @test all(((a, b), )->a <ₑ b,  combinations(args, 2))
end
