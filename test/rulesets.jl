@testset "Numeric" begin
    @syms a::Integer b c d x::Real y::Number
    @test simplify(x - y) == x + -1*y
    @test simplify(x - sin(y)) == x + -1*sin(y)
    @test simplify(-sin(x)) == -sin(x)
    @test simplify(1 * x * 2) == 2 * x
    @test simplify(1 + x + 2) == 3 + x
    @test simplify(b*b) == b^2 # tests merge_repeats
    @test simplify((a*b)^c) == a^c * b^c

    @test simplify(1x + 2x) == 3x
    @test simplify(3x + 2x) == 5x

    @test simplify(a + b + (x * y) + c + 2 * (x * y) + d)     == (3 * x * y) + a + b + c + d
    @test simplify(a + b + 2 * (x * y) + c + 2 * (x * y) + d) == (4 * x * y) + a + b + c + d

    @test simplify(a * x^y * b * x^d) == (a * b * (x ^ (d + y)))

    @test simplify(a + b + 0*c + d) == a + b + d
    @test simplify(a * b * c^0 * d) == a * b * d
    @test simplify(a * b * 1*c * d) == a * b * c * d
end

@testset "Pythagorean Identities" begin
    @syms a::Integer x::Real y::Number

    @test simplify(cos(x)^2 + 1 + sin(x)^2) == 2
    @test simplify(cos(y)^2 + 1 + sin(y)^2) == 2
    @test simplify(sin(y)^2 + cos(y)^2 + 1) == 2

    @test simplify(1 + y + tan(x)^2) == sec(x)^2 + y
    @test simplify(1 + y + cot(x)^2) == csc(x)^2 + y
end

#@testset "2π Identities" begin
#    @syms a::Integer x::Real y::Number
#
#    @test simplify(cos(x + 2π + a)) == cos(a + x)
#    @test simplify(tan(x + 2π * a)) == tan(x)
#end

@testset "Depth" begin
    @syms x
    R = RuleSet([@rule(sin(~x) => cos(~x)),
                 @rule( ~x + 1 => ~x - 1)])
    @test R(sin(sin(sin(x + 1)))) == cos(cos(cos(x - 1)))
    @test R(sin(sin(sin(x + 1))), depth=2) == cos(cos(sin(x + 1)))
end

@testset "RuleRewriteError" begin
    pred(x) = error("Fail")

    @syms a b

    rs = RuleSet([@rule ~x + ~y::pred => ~x])
    @test_throws SymbolicUtils.RuleRewriteError rs(a+b)
    err = try rs(a+b) catch err; err; end
    @test sprint(io->Base.showerror(io, err)) == "Failed to apply rule ~x + ~(y::pred) => ~x on expression (a + b)"
end

@testset "timerwrite" begin
    @syms a b c d
    expr1 = foldr((x,y)->rand([*, /])(x,y), rand([a,b,c,d], 100))
    SymbolicUtils.@timerewrite simplify(expr1)
end

using Random: shuffle

@testset "Shuffle Rules" begin
    @syms a::Integer b c d x::Real y::Number
    for _ ∈ 1:10
        R1 = RuleSet(SymbolicUtils.SIMPLIFY_RULES)
        R2 = RuleSet(shuffle(R1.rules))
        simplify_shuffle_tester(ex) = R1(ex) == R1(R2(ex))

        @test simplify_shuffle_tester(foldr((x,y)->rand([*, /, +, -, ^])(x,y), rand([a,b,c], 100)))
        
        @test simplify_shuffle_tester(x - y)
        @test simplify_shuffle_tester(x - sin(y))
        @test simplify_shuffle_tester(-sin(x)) 
        @test simplify_shuffle_tester(1 * x * 2)
        @test simplify_shuffle_tester(1 + x + 2)
        @test simplify_shuffle_tester(b*b)
        @test simplify_shuffle_tester((a*b)^c) 

        @test simplify_shuffle_tester(1x + 2x)
        @test simplify_shuffle_tester(3x + 2x)

        @test simplify_shuffle_tester(a + b + (x * y) + c + 2 * (x * y) + d)
        @test simplify_shuffle_tester(a + b + 2 * (x * y) + c + 2 * (x * y) + d)

        @test simplify_shuffle_tester(a * x^y * b * x^d)

        @test simplify_shuffle_tester(a + b + 0*c + d)
        @test simplify_shuffle_tester(a * b * c^0 * d)
        @test simplify_shuffle_tester(a * b * 1*c * d)
    end
end
