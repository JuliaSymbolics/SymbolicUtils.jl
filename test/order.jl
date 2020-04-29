using Test
using SymbolicUtils: <ₑ
SymbolicUtils.show_simplified[] = false

@syms a b c

function istotal(x,y)
    #either
    if x <ₑ y
        return !(y <ₑ x)
    elseif y <ₑ x
        return !(x <ₑ y) # already tested
    else
        # neither, equal
        return true
    end
end

@test istotal(a,a)
@test istotal(a,b)
@test istotal(2,a)
@test 2 <ₑ a
@test a <ₑ b
@test istotal(a, 2a)
@test 2a <ₑ a
@test istotal(b*a, a)
@test a <ₑ b*a 
@test !(b*a <ₑ b+a)

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
        @test !(b <ₑ f(2,b))
        for j in i+1:length(fs)
            g = fs[j]
            @test !(g(a, b) <ₑ f(a, b)) && !(f(a, b) <ₑ g(a, b))
            @test istotal(f(a, b), g(a, b))
        end
    end
end

@testset "0-arg variable calls ordering" begin
    @syms z() ρ()

    @test -1z() <ₑ ρ()
    @test !(ρ() <ₑ -1z())
end
