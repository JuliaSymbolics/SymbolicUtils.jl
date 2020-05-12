using Test
using SymbolicUtils: <ₑ
SymbolicUtils.show_simplified[] = false

@syms a b c

function istotal(x,y)
    # either
    if x <ₑ y
        return !(y <ₑ x)
    elseif y <ₑ x
        return !(x <ₑ y)
    else
        # "equal"
        return true
    end
end

@testset "term order" begin
    @syms a b c x y z
    @test a <ₑ x
end


@test istotal(a,a)
@test istotal(a,b)
@test istotal(2,a)
@test 2 <ₑ a
@test a <ₑ b
@test istotal(a, 2a)
@test a <ₑ 2a
@test istotal(b*a, a)
@test a <ₑ b*a 
@test !(b*a <ₑ b+a)
@test Term(^, [1,-1]) <ₑ a
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
            @test g(a, b) <ₑ f(a, b) && !(f(a, b) <ₑ g(a, b))
            @test istotal(f(a, b), g(a, b))
        end
    end
end

@testset "callable variable order" begin
    @syms z() ρ()

    @test -1z() <ₑ ρ()
    @test !(ρ() <ₑ -1z())

    @syms a(t) b(t) t
    @test a(t) <ₑ b(t)
    @test !(b(t) <ₑ a(t))
end

@testset "Sym vs Term" begin
    @syms x y

    @test x <ₑ (3 + x) && !((3 + x) <ₑ x)
    @test x^2 <ₑ y && !(y <ₑ x^2)

    # a nice consequence
    @test simplify(x/(x+3) + 3/(x+3)) == 1
end

@testset "small terms" begin
    # this failing was a cause of a nasty stackoverflow #82
    @syms a
    @test Term(^, [a, -1]) <ₑ (a + 2)
    @test !((a + 2) <ₑ Term(^, [a, -1]))
end
