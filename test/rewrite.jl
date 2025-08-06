using SymbolicUtils

include("utils.jl")

@syms a b c d x

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
    @eqtest @rule((~x*~y + ~x*~z)  => ~x * (~y+~z))(a*b + a*c) == a*(b+c)

    @eqtest @rule(+(~~x) => ~~x)(a + b) == [a,b]
    @eqtest @rule(+(~~x) => ~~x)(term(+, a, b, c)) == [a,b,c]
    @eqtest @rule(+(~~x,~y, ~~x) => (~~x, ~y))(term(+,9,8,9,type=Any)) == ([9,],8)
    @eqtest @rule(+(~~x,~y, ~~x) => (~~x, ~y, ~~x))(term(+,9,8,9,9,8,type=Any)) == ([9,8], 9, [9,8])
    @eqtest @rule(+(~~x,~y,~~x) => (~~x, ~y, ~~x))(term(+,6,type=Any)) == ([], 6, [])
end

@testset "Commutative + and *" begin
    r1 = @rule exp(sin(~x) + cos(~x)) => ~x
    # using a or x changes the order of the arguments in the call
    @test r1(exp(sin(a)+cos(a))) === a
    @test r1(exp(sin(x)+cos(x))) === x
    r2 = @rule (~x+~y)*(~z+~w)^(~m) => (~x, ~y, ~z, ~w, ~m)
    r3 = @rule (~z+~w)^(~m)*(~x+~y) => (~x, ~y, ~z, ~w, ~m)
    @test r2((a+b)*(x+c)^b) === (a, b, x, c, b)
    @test r3((a+b)*(x+c)^b) === (a, b, x, c, b)
    rPredicate1 = @rule ~x::(x->isa(x,Number)) + ~y => (~x, ~y)
    rPredicate2 = @rule ~y + ~x::(x->isa(x,Number)) => (~x, ~y)
    @test rPredicate1(2+x) === (2, x)
    @test rPredicate2(2+x) === (2, x)
    r5 = @rule (~y*(~z+~w))+~x => (~x, ~y, ~z, ~w)
    r6 = @rule ~x+((~z+~w)*~y) => (~x, ~y, ~z, ~w)
    @test r5(c*(a+b)+d) === (d, c, a, b)
    @test r6(c*(a+b)+d) === (d, c, a, b)
end

@testset "Slot matcher with default value" begin
    r_sum = @rule (~x + ~!y)^2 => ~y
    @test r_sum((a + b)^2) === b
    @test r_sum(b^2) === 0

    r_mult = @rule ~x * ~!y  => ~y
    @test r_mult(a * b) === b
    @test r_mult(a) === 1

    r_mult2 = @rule (~x * ~!y + ~z) => ~y
    @test r_mult2(c + a*b) === b
    @test r_mult2(c + b) === 1

    # here the "normal part" in the defslot_term_matcher is not a symbol but a tree
    r_mult3 = @rule (~!x)*(~y + ~z) => ~x
    @test r_mult3(a*(c+2)) === a
    @test r_mult3(2*(c+2)) === 2
    @test r_mult3(c+2) === 1
    
    r_pow = @rule (~x)^(~!m) => ~m
    @test r_pow(a^(b+1)) === b+1
    @test r_pow(a) === 1
    @test r_pow(a+1) === 1

    # here the "normal part" in the defslot_term_matcher is not a symbol but a tree
    r_pow2 = @rule (~x + ~y)^(~!m) => ~m
    @test r_pow2((a+b)^c) === c
    @test r_pow2(a+b) === 1

    r_mix = @rule (~x + (~y)*(~!c))^(~!m) => (~m, ~c)
    @test r_mix((a + b*c)^2) === (2, c)
    @test r_mix((a + b*c)) === (1, c)
    @test r_mix((a + b)) === (1, 1)

    r_more_than_two_arguments = @rule (~!a)*exp(~x)*sin(~x) => (~a, ~x)
    @test r_more_than_two_arguments(sin(x)*exp(x)) === (1, x)
    @test r_more_than_two_arguments(sin(x)*exp(x)*a) === (a, x)

    r_mixmix = @rule (~!a)*exp(~x)*sin(~!b + (~x)^2 + ~x) => (~a, ~b, ~x)
    @test r_mixmix(exp(x)*sin(1+x+x^2)*2) === (2, 1, x)
    @test r_mixmix(exp(x)*sin(x+x^2)*2) === (2, 0, x)
    @test r_mixmix(exp(x)*sin(x+x^2)) === (1, 0, x)

    r_predicate = @rule ~x + (~!m::(var->isa(var, Int))) => (~x, ~m)
    @test r_predicate(x+2) === (x, 2)
    @test r_predicate(x+2.0) !== (x, 2.0)
    # Note: r_predicate(x+2.0) doesnt return nothing, but (x+2.0, 0)
    # becasue of the defslot
end

@testset "power matcher with negative exponent" begin
    r1 = @rule (~x)^(~y) => (~x, ~y) # rule with slot as exponent
    @test r1(1/a^b) === (a, -b) # uses frankestein
    @test r1(1/a^(b+2c)) === (a, -b-2c) # uses frankestein
    @test r1(1/a^2) === (a, -2) # uses opposite_sign_matcher
    @test r1(1/a) === (a, -1)

    r2 = @rule (~x)^(~y + ~z) => (~x, ~y, ~z) # rule with term as exponent
    @test r2(1/a^(b+2c)) === (a, -b, -2c) # uses frankestein
    @test r2(1/a^3) === nothing # should use a term_matcher that flips the sign, but is not implemented

    r1defslot = @rule (~x)^(~!y) => (~x, ~y) # rule with defslot as exponent
    @test r1defslot(1/a^b) === (a, -b) # uses frankestein
    @test r1defslot(1/a^(b+2c)) === (a, -b-2c) # uses frankestein
    @test r1defslot(1/a^2) === (a, -2) # uses opposite_sign_matcher
    @test r1defslot(a) === (a, 1)

    r = @rule (~x + ~y)^(~m) => (~x, ~y, ~m) # rule to match (1/...)^(...)
    @test r((1/(a+b))^3) === (a,b,-3)
end

@testset "special power matches" begin
    r1 = @rule (~x)^(~y) => (~x, ~y)
    @test r1(exp(a)) === (ℯ, a) # uses exp_matcher
    @test r1(sqrt(a)) === (a, 1//2) # uses sqrt_matcher
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

    @test getmetadata(arguments(ex1)[1], MetaData) == :metadata

    ex = a * b
    ex = setmetadata(ex, MetaData, :metadata)
    ex1 = ex * c

    @test SymbolicUtils.isterm(ex1)
    @test getmetadata(arguments(ex1)[1], MetaData) == :metadata

    ex = a
    ex = setmetadata(ex, MetaData, :metadata)
    ex1 = ex * b

    @test getmetadata(arguments(ex1)[1], MetaData) == :metadata
end