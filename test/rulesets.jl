using Random: shuffle, seed!
using SymbolicUtils: getdepth, Rewriters, Term

@testset "Chain, Postwalk and Fixpoint" begin
    @syms w z α::Real β::Real

    r1 = @rule ~x + ~x => 2 * (~x)
    r2 = @acrule ~x * +(~~ys) => sum(map(y-> ~x * y,  ~~ys));

    rset = Rewriters.Postwalk(Rewriters.Chain([r2]))
    @test getdepth(rset) == typemax(Int)

    ex = 2 * (w + w + α + β)

    @eqtest rset(ex) == (((2 * w) + (2 * w)) + (2 * α)) + (2 * β)
    @eqtest Rewriters.Fixpoint(rset)(ex) == ((2 * (2 * w)) + (2 * α)) + (2 * β)
end

@testset "Numeric" begin
    @syms a::Integer b c d x::Real y::Number
    @eqtest simplify(Term{Real}(conj, [x])) == x
    @eqtest simplify(Term{Real}(real, [x])) == x
    @eqtest simplify(Term{Real}(imag, [x])) == 0
    @eqtest simplify(Term{Real}(imag, [y])) == imag(y)
    @eqtest simplify(x - y) == x + -1*y
    @eqtest simplify(x - sin(y)) == x + -1*sin(y)
    @eqtest simplify(-sin(x)) == -1*sin(x)
    @eqtest simplify(1 * x * 2) == 2 * x
    @eqtest simplify(1 + x + 2) == 3 + x
    @eqtest simplify(b*b) == b^2 # tests merge_repeats
    @eqtest simplify((a*b)^2) == a^2 * b^2
    @eqtest simplify((a*b)^c) == (a*b)^c

    @eqtest simplify(1x + 2x) == 3x
    @eqtest simplify(3x + 2x) == 5x

    @eqtest simplify(a + b + (x * y) + c + 2 * (x * y) + d)     == simplify((3 * x * y) + a + b + c + d)
    @eqtest simplify(a + b + 2 * (x * y) + c + 2 * (x * y) + d) == simplify((4 * x * y) + a + b + c + d)

    @eqtest simplify(a * x^y * b * x^d) == simplify(a * b * (x ^ (d + y)))

    @eqtest simplify(a + b + 0*c + d) == simplify(a + b + d)
    @eqtest simplify(a * b * c^0 * d) == simplify(a * b * d)
    @eqtest simplify(a * b * 1*c * d) == simplify(a * b * c * d)
    @eqtest simplify_fractions(x^2.0/(x*y)^2.0) == simplify_fractions(1 / (y^2.0))

    @test simplify(Term(one, [a])) == 1
    @test simplify(Term(one, [b+1])) == 1
    @test simplify(Term(one, [x+2])) == 1


    @test simplify(Term(zero, [a])) == 0
    @test simplify(Term(zero, [b+1])) == 0
    @test simplify(Term(zero, [x+2])) == 0
end

@testset "boolean" begin
    @syms a::Real b c

    @eqtest simplify(a < 0) == (a < 0)
    @eqtest simplify(0 < a) == (0 < a)
    @eqtest simplify((0 < a) | true) == true
    @eqtest simplify(true | (0 < a)) == true
    @eqtest simplify((0 < a) & true) == (0 < a)
    @eqtest simplify(true & (0 < a)) == (0 < a)
    @eqtest simplify(false & (0 < a)) == false
    @eqtest simplify((0 < a) & false) == false
    @eqtest simplify(Term{Bool}(!, [true])) == false
    @eqtest simplify(Term{Bool}(|, [false, true])) == true
    @eqtest simplify(ifelse(true, a,b)) == a
    @eqtest simplify(ifelse(false, a,b)) == b

    # abs
    @test simplify(substitute(ifelse(!(a < 0), a,-a), Dict(a=>-1))) == 1
    @test simplify(substitute(ifelse(!(a < 0), a,-a), Dict(a=>1))) == 1
    @test simplify(substitute(ifelse(a < 0, -a, a), Dict(a=>-1))) == 1
    @test simplify(substitute(ifelse(a < 0, -a, a), Dict(a=>1))) == 1
end

@testset "Pythagorean Identities" begin
    @syms a::Integer x::Real y::Number

    @test simplify(cos(x)^2 + 1 + sin(x)^2) == 2
    @test simplify(cos(y)^2 + 1 + sin(y)^2) == 2
    @test simplify(sin(y)^2 + cos(y)^2 + 1) == 2

    @eqtest simplify(1 + y + tan(x)^2) == sec(x)^2 + y
    @eqtest simplify(1 + y + cot(x)^2) == csc(x)^2 + y
    @eqtest simplify(cos(x)^2 - 1) == -sin(x)^2
    @eqtest simplify(sin(x)^2 - 1) == -cos(x)^2
end

@testset "Double angle formulas" begin
    @syms r x
    @eqtest simplify(r*cos(x/2)^2 - r*sin(x/2)^2) == r*cos(x)
    @eqtest simplify(r*sin(x/2)^2 - r*cos(x/2)^2) == -r*cos(x)
    @eqtest simplify(2cos(x)*sin(x)) == sin(2x)
end

@testset "Exponentials" begin
    @syms a::Real b::Real
    @eqtest simplify(exp(a)*exp(b)) == simplify(exp(a+b))
    @eqtest simplify(exp(a)*exp(a)) == simplify(exp(2a))
    @test simplify(exp(a)*exp(-a)) == 1
    @eqtest simplify(exp(a)^2) == simplify(exp(2a))
    @eqtest simplify(exp(a) * a * exp(b)) == simplify(a*exp(a+b))
end

@testset "Div, Mod & Rem" begin
    @syms x::Integer y::Integer z::Integer u::Real w
    @testset "single integer term" begin
        for n in (-7, -1, 1, 2), m in (-6, -1, 1, 3)
            @test simplify(mod(n * m * x, m)) == 0
            @test simplify(rem(n * m * x, m)) == 0
            @eqtest simplify(div(n * m * x, m)) == n * x
            @test simplify(mod(-n * m * x, m)) == 0
            @test simplify(rem(-n * m * x, m)) == 0
            @eqtest simplify(div(-n * m * x, m)) == -n * x
            @eqtest simplify(mod(mod(n * x, m), m)) == simplify(mod(n * x, m))
            @eqtest simplify(rem(rem(n * x, m), m)) == simplify(rem(n * x, m))
        end
    end
    @testset "single real term" begin
        @eqtest simplify(mod(u, 1)) == mod(u, 1)
        @eqtest simplify(rem(u, 1)) == rem(u, 1)
        @eqtest simplify(div(u, 1)) == div(u, 1)
        @eqtest simplify(mod(2 * u, 2)) == mod(2 * u, 2)
        @eqtest simplify(rem(2 * u, 2)) == rem(2 * u, 2)
        @eqtest simplify(div(2 * u, 2)) == div(2 * u, 2)
    end
    @testset "several terms" begin
        for n in (-3, 2), m in (-1, 1, 3)
            @test simplify(mod(m * (n * x + 2 * n * y + x * y), m)) == 0
            @test simplify(rem(m * (n * x + 2 * n * y + x * y), m)) == 0
            @eqtest simplify(div(m * (n * x + 2 * n * y + x * y), m)) == simplify(n * x + 2 * n * y + x * y)
            @eqtest simplify(mod(mod(n * x, m) + mod(y, m), m)) == simplify(mod(n * x + y, m))
            @eqtest simplify(rem(rem(n * x, m) + rem(y, m), m)) == simplify(rem(n * x + y, m))
        end
    end
    @testset "div + rem" begin
        for n in (1, 2), m in (1, 3)
            @eqtest simplify(m * div(n * x, m) + rem(n * x, m)) == n * x
            @eqtest simplify(m * div(n * u, m) + rem(n * u, m)) == n * u
            @eqtest simplify(m * div(0.5 * n * u, m) + rem(0.5 * n * u, m)) == 0.5 * n * u
            @eqtest simplify(m * div(n * w, m) + rem(n * w, m)) == m * div(n * w, m) + rem(n * w, m)
        end
        @eqtest simplify(5div(21*x*y + z + 13x + 7x * z, 5) + rem(21*x*y + z + 13x + 7x * z, 5)) == z + 13x + 7x*z + 21x*y
        @eqtest simplify(5div(x + y, 2) + rem(x + y, 2)) == x + y + 3 * div(x + y, 2)
        @eqtest simplify(5div(x + y, 2) + 2rem(x + y, 2)) == x + y + div(x + y, 2)
        @eqtest simplify(div(x + y, 2) + 2rem(x + y, 2)) == x + y - 3 * div(x + y, 2)
        @eqtest simplify(div(x + y, 2) + rem(x + y, 2)) == x + y - div(x + y, 2)
    end
    @testset "miscellaneous" begin
        @eqtest simplify(mod(21*x*y + z + 13x + 7x * z, 5)) == mod(z + 3x + x*y + 2x*z, 5)
        @eqtest simplify(rem(21*x*y + z + 13x + 7x * z, -3)) == simplify(rem(x + z + x * z, -3))
        @eqtest simplify(div(17*x*y + z + 12x + 7x * z, 2)) == 6x + 3x*z + 8x*y + div(z + x*(y + z), 2)
        @eqtest simplify(div(2*x + 2w, 2)) == div(2w + 2x, 2)
        @eqtest simplify(div(2*x + y, 2) + sin(x)^2 + cos(x)^2 + 1) == 2 + x + div(y, 2)
        @eqtest simplify(mod(mod(x, 5) + mod(div(7y, 3), 5), 5)) == simplify(mod(x + 2y + div(y, 3), 5))
        @eqtest simplify(div(x + sin(2x)^2 + cos(2x)^2, exp(x)*exp(-x))) == 1 + x
        @eqtest simplify(2div(cos(x), 2) + rem(cos(x), 2)) == cos(x)
        @test simplify(cos(div(x, 2))^2 + sin(div(x, 2))^2) == 1
    end
end

@testset "simplify_fractions" begin
    @syms x y z
    @eqtest simplify(2*((y + z)/x) - 2*y/x - z/x*2) == 0
end

@testset "Depth" begin
    @syms x
    R = Rewriters.Postwalk(Rewriters.Chain([@rule(sin(~x) => cos(~x)),
                                            @rule(1 + ~x => ~x - 1)]))
    @eqtest R(sin(sin(sin(x + 1)))) == cos(cos(cos(x - 1)))
    #@eqtest R(sin(sin(sin(x + 1))), depth=2) == cos(cos(sin(x + 1)))
end

pred(x) = error("Fail")
@testset "RuleRewriteError" begin
    using Metatheory
    @syms a b

    rs = Rewriters.Postwalk(Rewriters.Chain(([@rule ~x + ~y::pred => ~x])))
    @test_throws Metatheory.Rules.RuleRewriteError rs(a+b)
    err = try rs(a+b) catch err; err; end
    @test sprint(io->Base.showerror(io, err)) == "Failed to apply rule ~x + ~(y::pred) => ~x on expression a + b"
end

@testset "Threading" begin
    @syms a b c d
    ex = (((0.6666666666666666 / (c / 1)) + ((1 * a) / (c / 1))) +
          (1.0 / (((1 * d) / (1 + b)) * (1 / b)))) +
          ((((1 * a) + (1 * a)) / ((2.0 * (d + 1)) / 1.0)) +
           ((((d * 1) / (1 + c)) * 2.0) / ((1 / d) + (1 / c))))
    @eqtest simplify(ex) == simplify(ex, threaded=true, thread_subtree_cutoff=3)
    @test SymbolicUtils.node_count(a + b * c / d) == 7
end

@testset "timerwrite" begin
    @syms a b c d
    expr1 = foldr((x,y)->rand([*, /])(x,y), rand([a,b,c,d], 100))
    SymbolicUtils.@timerewrite simplify(expr1)
end


_g(y) = sin
@testset "interpolation" begin
    @syms a

    @test isnothing(@rule(_g(1)(a) => 2)(sin(a)))
    @test @rule($(_g(1))(a) => 2)(sin(a)) == 2
end

_f(x) = x === a
@testset "where" begin
    using Metatheory
    expected = :(_f(~x) ? ~x + ~y : nothing)
    @test Metatheory.Syntax.rewrite_rhs(:((~x + ~y) where _f(~x))) == expected

    @syms a b
    r = @rule ~x => ~x where _f(~x)
    @eqtest r(a) == a
    @test isnothing(r(b))

    r = @acrule ~x => ~x where _f(~x)
    @eqtest r(a) == a
    @test r(b) === nothing
end
