using Random: shuffle, seed!
using SymbolicUtils: getdepth, Rewriters, Term

@testset "Chain, Postwalk and Fixpoint" begin
    @syms w z α::Real β::Real

    r1 = @rule ~x + ~x => 2 * (~x)
    r2 = @acrule ~x * +(~~ys) => sum(map(y -> ~x * y, ~~ys))

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
    @eqtest simplify(x - y) == x + -1 * y
    @eqtest simplify(x - sin(y)) == x + -1 * sin(y)
    @eqtest simplify(-sin(x)) == -1 * sin(x)
    @eqtest simplify(1 * x * 2) == 2 * x
    @eqtest simplify(1 + x + 2) == 3 + x
    @eqtest simplify(b * b) == b^2 # tests merge_repeats
    @eqtest simplify((a * b)^2) == a^2 * b^2
    @eqtest simplify((a * b)^c) == (a * b)^c

    @eqtest simplify(1x + 2x) == 3x
    @eqtest simplify(3x + 2x) == 5x

    @eqtest simplify(a + b + (x * y) + c + 2 * (x * y) + d) == simplify((3 * x * y) + a + b + c + d)
    @eqtest simplify(a + b + 2 * (x * y) + c + 2 * (x * y) + d) == simplify((4 * x * y) + a + b + c + d)

    @eqtest simplify(a * x^y * b * x^d) == simplify(a * b * (x^(d + y)))

    @eqtest simplify(a + b + 0 * c + d) == simplify(a + b + d)
    @eqtest simplify(a * b * c^0 * d) == simplify(a * b * d)
    @eqtest simplify(a * b * 1 * c * d) == simplify(a * b * c * d)
    @eqtest simplify_fractions(x^2.0 / (x * y)^2.0) == simplify_fractions(1 / (y^2.0))

    @test simplify(Term(one, [a])) == 1
    @test simplify(Term(one, [b + 1])) == 1
    @test simplify(Term(one, [x + 2])) == 1


    @test simplify(Term(zero, [a])) == 0
    @test simplify(Term(zero, [b + 1])) == 0
    @test simplify(Term(zero, [x + 2])) == 0
end

@testset "LiteralReal" begin
    @syms x1::LiteralReal x2::LiteralReal
    s = cos(x1 * 3.2) - x2 * 5.8 + x2 * 1.2
    @eqtest s == cos(x1 * 3.2) - x2 * 5.8 + x2 * 1.2

    # Prevents automatic simplification:
    @eqtest s != cos(3.2(x1^1)) - 4.6x2

    # However, manual simplification should still work:
    @eqtest simplify(s) == simplify(cos(3.2x1) - 4.6x2)
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
    @eqtest simplify(ifelse(true, a, b)) == a
    @eqtest simplify(ifelse(false, a, b)) == b

    # abs
    @test simplify(substitute(ifelse(!(a < 0), a, -a), Dict(a => -1))) == 1
    @test simplify(substitute(ifelse(!(a < 0), a, -a), Dict(a => 1))) == 1
    @test simplify(substitute(ifelse(a < 0, -a, a), Dict(a => -1))) == 1
    @test simplify(substitute(ifelse(a < 0, -a, a), Dict(a => 1))) == 1
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
    @eqtest simplify(r * cos(x / 2)^2 - r * sin(x / 2)^2) == r * cos(x)
    @eqtest simplify(r * sin(x / 2)^2 - r * cos(x / 2)^2) == -r * cos(x)
    @eqtest simplify(2cos(x) * sin(x)) == sin(2x)
end

@testset "Exponentials" begin
    @syms a::Real b::Real
    @eqtest simplify(exp(a) * exp(b)) == simplify(exp(a + b))
    @eqtest simplify(exp(a) * exp(a)) == simplify(exp(2a))
    @test simplify(exp(a) * exp(-a)) == 1
    @eqtest simplify(exp(a)^2) == simplify(exp(2a))
    @eqtest simplify(exp(a) * a * exp(b)) == simplify(a * exp(a + b))
    @eqtest simplify(one(Int)^a) == 1
    @eqtest simplify(one(Complex{Float64})^a) == 1
    @eqtest simplify(a^b * 1^a) == a^b
end

@testset "simplify_fractions" begin
    @syms x y z
    @eqtest simplify(2 * ((y + z) / x) - 2 * y / x - z / x * 2) == 0
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
    @syms a b

    rs = Rewriters.Postwalk(Rewriters.Chain(([@rule ~x + ~y::pred => ~x])))
    @test_throws SymbolicUtils.RuleRewriteError rs(a + b)
    err = try
        rs(a + b)
    catch err
        err
    end
    @test sprint(io -> Base.showerror(io, err)) == "Failed to apply rule ~x + ~(y::pred) => ~x on expression a + b"
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
    expr1 = foldr((x, y) -> rand([*, /])(x, y), rand([a, b, c, d], 100))
    SymbolicUtils.@timerewrite simplify(expr1)
end


_g(y) = sin
@testset "interpolation" begin
    @syms a

    @test isnothing(@rule(_g(1)(a) => 2)(sin(a)))
    @test @rule($(_g(1))(a) => 2)(sin(a)) == 2
end

@syms a
_f(x) = x === a
@testset "where" begin

    @syms a b
    r = @rule ~x => ~x where {_f(~x)}
    @eqtest r(a) == a
    @test isnothing(r(b))

    r = @acrule ~x => ~x where {_f(~x)}
    @eqtest r(a) == a
    @test r(b) === nothing
end
