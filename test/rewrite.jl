using SymbolicUtils
using Test 
include("utils.jl")

@syms a b c

@testset "Equality" begin
    @eqtest a == a
    @eqtest a != b
    @eqtest a*b == a*b
    @eqtest a*b != a
    @eqtest a != a*b
end

@testset "Literal Matcher" begin
    r = @rule 1 => 4
    @test r(1) === 4
    @test r(1.0) === 4
    @test r(2) === nothing
end

@testset "Slot matcher" begin
    @test @rule(~x => true)("?") === true
    @test @rule( ~x => ~x)(2) === 2
end

@testset "Term matcher" begin
    @test @rule(sin(~x) => ~x)(sin(a)) === a
    @eqtest @rule(sin(~x) => ~x)(sin(a^2)) == a^2
    @test @rule(sin(~x) => ~x)(sin(a)^2) === nothing
    @test @rule(sin(sin(~x)) => ~x)(sin(a^2)) === nothing
    @test @rule(sin(sin(~x)) => ~x)(sin(sin(a))) === a
    @test @rule(sin(~x)^2 => ~x)(sin(a)^2) === a
end

@testset "Equality matching" begin
    @test @rule((~x)^(~x) => ~x)(a^a) === a
    @test @rule((~x)^(~x) => ~x)(b^a) === nothing
    @test @rule((~x)^(~x) => ~x)(a+a) === nothing
    @eqtest @rule((~x)^(~x) => ~x)(sin(a)^sin(a)) == sin(a)
    @eqtest @rule((~x*~y + ~z*~x)  => ~x * (~y+~z))(a*b + a*c) == a*(b+c)

    @test issetequal(@rule(+(~~x) => ~~x)(a + b), [a,b])
    @eqtest @rule(+(~~x) => ~~x)(term(+, a, b, c)) == [a,b,c]
    @eqtest @rule(+(~~x,~y, ~~x) => (~~x, ~y))(term(+,9,8,9,type=Any)) == ([9,],8)
    @eqtest @rule(+(~~x,~y, ~~x) => (~~x, ~y, ~~x))(term(+,9,8,9,9,8,type=Any)) == ([9,8], 9, [9,8])
    @eqtest @rule(+(~~x,~y,~~x) => (~~x, ~y, ~~x))(term(+,6,type=Any)) == ([], 6, [])
end

@testset "Slot matcher with default value" begin
    r_sum = @rule (~x + ~!y)^2 => ~y
    @test r_sum((a + b)^2) in Set([a, b])
    @test r_sum(b^2) === 0

    r_mult = @rule ~x * ~!y  => ~y
    @test r_mult(a * b) in Set([a, b])
    @test r_mult(a) === 1

    r_mult2 = @rule (~x * ~!y + ~z) => ~y
    # can match either `a` or `b` or coefficient of `c`
    @test r_mult2(c + a*b) in Set([1, a, b])
    @test r_mult2(c + b) === 1

    # here the "normal part" in the defslot_term_matcher is not a symbol but a tree
    r_mult3 = @rule (~!x)*(~y + ~z) => ~x
    @test r_mult3(a*(c+2)) === a
    @test r_mult3(2*(c+2)) === 2
    @test r_mult3(c+2) === 1
    
    r_pow = @rule (~x)^(~!m) => ~m
    @test isequal(r_pow(a^(b+1)), b+1)
    @test r_pow(a) === 1
    @test r_pow(a+1) === 1

    # here the "normal part" in the defslot_term_matcher is not a symbol but a tree
    r_pow2 = @rule (~x + ~y)^(~!m) => ~m
    @test r_pow2((a+b)^c) === c
    @test r_pow2(a+b) === 1

    r_mix = @rule (~x + (~y)*(~!c))^(~!m) => ~m + ~c
    @test r_mix((a + b*c)^2) in Set([2 + b, 3, 2 + c])
    @test r_mix((a + b*c)) in Set([1 + b, 1 + c])
    @test r_mix((a + b)) === 2 #1+1
end

using SymbolicUtils: @capture

@testset "Capture form" begin

    ex = a^a

    #note that @test inserts a soft local scope (try-catch) that would gobble
    #the matches from assignment statements in @capture macro, so we call it
    #outside the test macro 
    ret = @capture ex (~x)^(~x)
    @test ret
    @test @isdefined x
    @test x === a

    ex = b^a
    ret = @capture ex (~y)^(~y)
    @test !ret
    @test !(@isdefined y)

    ret = @capture (a + b) (+)(~~z)
    @test ret
    @test @isdefined z
    @test all(z .=== arguments(a + b))

    #a more typical way to use the @capture macro

    f(x) = if @capture x (~w)^(~w)
        w
    end

    @eqtest f(b^b) == b
    @test f(b+b) == nothing
end

@testset "Rewriter tweaks #548" begin
    struct MetaData end
    ex = a + b
    ex = setmetadata(ex, MetaData, :metadata)
    ex1 = ex + c

    @test SymbolicUtils.isterm(ex1)
    @test getmetadata(arguments(ex1)[1], MetaData) == :metadata

    ex = a
    ex = setmetadata(ex, MetaData, :metadata)
    ex1 = ex + b

    @test getmetadata(sorted_arguments(ex1)[1], MetaData) == :metadata

    ex = a * b
    ex = setmetadata(ex, MetaData, :metadata)
    ex1 = ex * c

    @test SymbolicUtils.isterm(ex1)
    @test getmetadata(arguments(ex1)[1], MetaData) == :metadata

    ex = a
    ex = setmetadata(ex, MetaData, :metadata)
    ex1 = ex * b

    @test getmetadata(sorted_arguments(ex1)[1], MetaData) == :metadata
end
