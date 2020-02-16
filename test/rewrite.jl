@vars a b c

@testset "Equality" begin
    @test a == a
    @test a != b
    @test a*b == a*b
    @test a*b != a
    @test a != a*b
end

@testset "Literal Matcher" begin
    #r = rewriter(Rule(1, d->4, ()))
    r = rewriter(@rule 1 => 4)
    @test r(1) === 4
    @test r(1.0) === 4
    @test r(2) === nothing
end

# Slot matcher
@testset "Equality" begin
    @test rewriter(@rule ~x => true)("?") === true
    @test rewriter(@rule ~x => ~x)(2) === 2
end

# Term matcher
@testset "Equality" begin
    @test rewriter(@rule sin(~x) => ~x)(sin(a)) === a
    @test rewriter(@rule sin(~x) => ~x)(sin(a^2)) == a^2
    @test rewriter(@rule sin(~x) => ~x)(sin(a)^2) === nothing
    @test rewriter(@rule sin(sin(~x)) => ~x)(sin(a^2)) === nothing
    @test rewriter(@rule sin(sin(~x)) => ~x)(sin(sin(a))) === a
    @test rewriter(@rule sin(~x)^2 => ~x)(sin(a)^2) === a
end

# Equality matching
@testset "Equality" begin
    @test rewriter(@rule (~x)^(~x) => ~x)(a^a) === a
    @test rewriter(@rule (~x)^(~x) => ~x)(b^a) === nothing
    @test rewriter(@rule (~x)^(~x) => ~x)(a+a) === nothing
    @test rewriter(@rule (~x)^(~x) => ~x)(sin(a)^sin(a)) == sin(a)
    @test rewriter(@rule (~x*~y + ~x*~z)  => ~x * (~y+~z))(a*b + a*c) == a*(b+c)

    @test rewriter(@rule +(~~x) => ~~x)(a + b) == [a,b]
    @test rewriter(@rule +(~~x) => ~~x)(a + b + c) == [a,b,c]
    @test rewriter(@rule +(~~x) => ~~x)(+(a, b, c)) == [a,b,c]
    @test rewriter(@rule +(~~x,~y, ~~x) => (~~x, ~y))(term(+,9,8,9,type=Any)) == ([9,],8)
    @test rewriter(@rule +(~~x,~y, ~~x) => (~~x, ~y, ~~x))(term(+,9,8,9,9,8,type=Any)) == ([9,8], 9, [9,8])
    @test rewriter(@rule +(~~x,~y,~~x) => (~~x, ~y, ~~x))(term(+,6,type=Any)) == ([], 6, [])
end
