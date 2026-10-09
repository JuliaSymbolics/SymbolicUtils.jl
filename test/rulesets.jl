using Random: shuffle, seed!
using SymbolicUtils
using SymbolicUtils: getdepth, Rewriters, Term, unwrap_const

include("utils.jl")

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
    @syms a::Integer b c d x::Real y::Number z
    # Integral-rational normalization must work when rational forms are interned
    # first (no prior Int coeff/exponent for these shapes in the hash-cons cache).
    has_integral_rational(ex) = !SymbolicUtils.iscall(ex) ?
        (unwrap_const(ex) isa Rational && denominator(unwrap_const(ex)) == 1) :
        any(has_integral_rational, arguments(ex))
    @test unwrap_const(simplify(1 // 1)) === 1
    integral_rational_sum = simplify((1 // 1) + x)
    @test any(arg -> unwrap_const(arg) === 1, arguments(integral_rational_sum))
    @test unwrap_const(last(arguments(simplify(x^(2 // 1))))) === 2
    fractional_rational_sum = simplify((1 // 2) + x)
    @test any(arg -> unwrap_const(arg) === 1 // 2, arguments(fractional_rational_sum))
    rational_coefficients = simplify((2 // 1) * x + (3 // 1) * y)
    @test !has_integral_rational(rational_coefficients)
    @test isequal(2 * x, (2 // 1) * x) # non-full isequal still ignores coeff type
    @test !has_integral_rational(simplify(x^(2 // 1) * y))
    @test isequal(simplify(x^(2 // 1) * y), x^2 * y)
    @test !has_integral_rational(simplify(sin((2 // 1) * x + (3 // 1) * y)))
    @test !has_integral_rational(simplify(((2 // 1) * x + y) / z))
    @test !has_integral_rational(simplify(x^(1 // 2) * x^(3 // 2) * y + z))
    @syms A[1:2]
    @test !has_integral_rational(simplify((2 // 1) * A[1] + A[2]))
    @test !has_integral_rational(simplify((1 // 1) + x; rewriter = Rewriters.Empty()))
    typed_term = Term{SymReal}(identity, [x, 2 // 1]; type = Complex{Float64})
    @test SymbolicUtils.symtype(simplify(typed_term)) === Complex{Float64}

    @eqtest simplify(Term{SymReal}(conj, [x]; type = Real)) == x
    @eqtest simplify(Term{SymReal}(real, [x]; type = Real)) == x
    @eqtest unwrap_const(simplify(Term{SymReal}(imag, [x]; type = Real))) == 0
    @eqtest simplify(Term{SymReal}(imag, [y]; type = Real)) == imag(y)
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

    # Issue JuliaSymbolics/Symbolics.jl#1815: x^a * x should simplify to x^(a + 1)
    @eqtest simplify(x^a * x) == simplify(x^(a + 1))
    @eqtest simplify(x * x^a) == simplify(x^(a + 1))

    @eqtest simplify(a + b + 0 * c + d) == simplify(a + b + d)
    @eqtest simplify(a * b * c^0 * d) == simplify(a * b * d)
    @eqtest simplify(a * b * 1 * c * d) == simplify(a * b * c * d)
    @eqtest simplify_fractions(x^2.0 / (x * y)^2.0) == simplify_fractions(1 / (y^2.0))

    @test unwrap_const(simplify(Term{SymReal}(one, [a]))) == 1
    @test unwrap_const(simplify(Term{SymReal}(one, [b + 1]))) == 1
    @test unwrap_const(simplify(Term{SymReal}(one, [x + 2]))) == 1


    @test unwrap_const(simplify(Term{SymReal}(zero, [a]))) == 0
    @test unwrap_const(simplify(Term{SymReal}(zero, [b + 1]))) == 0
    @test unwrap_const(simplify(Term{SymReal}(zero, [x + 2]))) == 0
end

@testset "Issue #633: trig simplification is independent of symbol names" begin
    for names in ((:r, :th, :phi), (Symbol("#1#"), Symbol("#2#"), Symbol("#3#")))
        r, th, phi = (SymbolicUtils.Sym{SymbolicUtils.SymReal}(name; type = Real) for name in names)
        expressions = (
            cos(th)^2 + cos(phi)^2 * sin(th)^2 + sin(th)^2 * sin(phi)^2,
            -r*cos(th)*sin(th) + r*cos(th)*cos(phi)^2*sin(th) + r*cos(th)*sin(th)*sin(phi)^2,
            r^2*sin(th)^2 + r^2*cos(th)^2*cos(phi)^2 + r^2*cos(th)^2*sin(phi)^2,
            r^2*cos(phi)^2*sin(th)^2 + r^2*sin(th)^2*sin(phi)^2,
        )

        @test unwrap_const(simplify(expressions[1])) == 1
        @test isequal(unwrap_const(simplify(expressions[2])), 0)
        @test isequal(simplify(expressions[3]), r^2)
        @test isequal(simplify(expressions[4]), r^2 * sin(th)^2)
    end
end

@testset "Trig factoring applies inside larger sums" begin
    @syms a::Real c::Real r::Real x::Real
    expressions = (
        c + r*cos(x)^2 - r*sin(x)^2,
        a + r*sin(x)^2 - r*cos(x)^2,
        c + r*tan(x)^2 - r*sec(x)^2,
        c + r*cot(x)^2 - r*csc(x)^2,
        a + r*cosh(x)^2 - r*sinh(x)^2,
    )
    expected = (
        c + r*cos(2x),
        a - r*cos(2x),
        c - r,
        c - r,
        a + r,
    )

    for (expression, result) in zip(expressions, expected)
        @test isequal(simplify(expression), result)
    end
    @test isequal(simplify(sum(r*sin(i*x)^2 + r*cos(i*x)^2 for i in 1:5)), 5r)
end

@testset "LiteralReal" begin
    @syms x1 x2 vartype=TreeReal
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
    @eqtest unwrap_const(simplify((0 < a) | true)) == true
    @eqtest unwrap_const(simplify(true | (0 < a))) == true
    @eqtest simplify((0 < a) & true) == (0 < a)
    @eqtest simplify(true & (0 < a)) == (0 < a)
    @eqtest unwrap_const(simplify(false & (0 < a))) == false
    @eqtest unwrap_const(simplify((0 < a) & false)) == false
    @eqtest unwrap_const(simplify(Term{SymReal}(!, [true]; type = Bool))) == false
    @eqtest unwrap_const(simplify(Term{SymReal}(|, [false, true]; type = Bool))) == true
    @eqtest simplify(ifelse(true, a, b)) == a
    @eqtest simplify(ifelse(false, a, b)) == b

    # abs
    @test unwrap_const(simplify(substitute(ifelse(!(a < 0), a, -a), Dict(a => -1)))) == 1
    @test unwrap_const(simplify(substitute(ifelse(!(a < 0), a, -a), Dict(a => 1)))) == 1
    @test unwrap_const(simplify(substitute(ifelse(a < 0, -a, a), Dict(a => -1)))) == 1
    @test unwrap_const(simplify(substitute(ifelse(a < 0, -a, a), Dict(a => 1)))) == 1
end

@testset "Pythagorean Identities" begin
    @syms a::Integer x::Real y::Number

    @test unwrap_const(simplify(cos(x)^2 + 1 + sin(x)^2)) == 2
    @test unwrap_const(simplify(cos(y)^2 + 1 + sin(y)^2)) == 2
    @test simplify(2x*cos(y)^2 + 1 + 2x*sin(y)^2) == 1 + 2x
    @test unwrap_const(simplify(sin(y)^2 + cos(y)^2 + 1)) == 2

    # Coefficient -1 distributes into Add, so factoring through r*(sin^2+cos^2)
    # never sees the unscaled sum; the direct scaled Pythagorean rule covers it.
    @test unwrap_const(simplify(-sin(x)^2 - cos(x)^2)) == -1
    @test unwrap_const(simplify(-(sin(x)^2 + cos(x)^2))) == -1
    @eqtest simplify(y - sin(x)^2 - cos(x)^2) == y - 1
    @test unwrap_const(simplify(-2sin(x)^2 - 2cos(x)^2)) == -2

    @eqtest simplify(1 + y + tan(x)^2) == sec(x)^2 + y
    @eqtest simplify(1 + y + cot(x)^2) == csc(x)^2 + y
    @eqtest simplify(cos(x)^2 - 1) == -sin(x)^2
    @eqtest simplify(sin(x)^2 - 1) == -cos(x)^2

    # tan²−sec² = −1 and cot²−csc² = −1 (not +1)
    @test unwrap_const(simplify(tan(x)^2 - sec(x)^2)) == -1
    @test unwrap_const(simplify(sec(x)^2 - tan(x)^2)) == 1
    @test unwrap_const(simplify(cot(x)^2 - csc(x)^2)) == -1
    seed!(1131)
    for _ in 1:20
        t = 2π * rand()
        abs(cos(t)) < 0.2 && continue
        abs(sin(t)) < 0.2 && continue
        @test Float64(unwrap_const(substitute(simplify(tan(x)^2 - sec(x)^2), Dict(x => t)))) ≈
              (tan(t)^2 - sec(t)^2) atol=1e-10
        @test Float64(unwrap_const(substitute(simplify(cot(x)^2 - csc(x)^2), Dict(x => t)))) ≈
              (cot(t)^2 - csc(t)^2) atol=1e-10
    end

    # 1 - cos² / sin² and scaled a - a*trig²
    @eqtest simplify(1 - cos(x)^2) == sin(x)^2
    @eqtest simplify(1 - sin(x)^2) == cos(x)^2
    @eqtest simplify(2 - 2cos(x)^2) == 2sin(x)^2
    @eqtest simplify(2 - 2sin(x)^2) == 2cos(x)^2
    @eqtest simplify(a - a*sin(x)^2) == a*cos(x)^2
    @eqtest simplify(a - a*cos(x)^2) == a*sin(x)^2
    @eqtest simplify(3 - 2cos(x)^2) == 3 - 2cos(x)^2
    # 2a - 2a*cos² needs a scaled-coeff rule; omitted (perf vs coverage trade-off)

    @eqtest unwrap_const(simplify(cosh(x)^2 + 1 - sinh(x)^2)) == 2
    @eqtest unwrap_const(simplify(cosh(y)^2 + 1 - sinh(y)^2)) == 2
    @eqtest unwrap_const(simplify(-sinh(y)^2 + cosh(y)^2 + 1)) == 2

    @eqtest simplify(cosh(x)^2 - 1) == sinh(x)^2
    @eqtest simplify(sinh(x)^2 + 1) == cosh(x)^2
end

@testset "Double angle formulas" begin
    @syms r x

    @eqtest simplify(r * cos(x / 2)^2 - r * sin(x / 2)^2) == r * cos(x)
    @eqtest simplify(r * sin(x / 2)^2 - r * cos(x / 2)^2) == -r * cos(x)
    @eqtest simplify(2cos(x) * sin(x)) == sin(2x)

    @eqtest simplify(r * cosh(x / 2)^2 + r * sinh(x / 2)^2) == r * cosh(x)
    @eqtest simplify(r * sinh(x / 2)^2 + r * cosh(x / 2)^2) == r * cosh(x)
    @eqtest simplify(2cosh(x) * sinh(x)) == sinh(2x)
end

@testset "Exponentials" begin
    @syms a::Real b::Real
    @eqtest simplify(exp(a) * exp(b)) == simplify(exp(a + b))
    @eqtest simplify(exp(a) * exp(a)) == simplify(exp(2a))
    @test unwrap_const(simplify(exp(a) * exp(-a))) == 1
    @eqtest simplify(exp(a)^2) == simplify(exp(2a))
    @eqtest simplify(exp(a) * a * exp(b)) == simplify(a * exp(a + b))
    @eqtest unwrap_const(simplify(one(Int)^a)) == 1
    @eqtest unwrap_const(simplify(one(Complex{Float64})^a)) == 1
    @eqtest simplify(a^b * 1^a) == a^b

    # Fractional and nested powers shouldn't unconditionally fold
    # See https://github.com/JuliaSymbolics/SymbolicUtils.jl/pull/1077
    @eqtest simplify((a^2)^(1//2)) == abs(a)
    @eqtest simplify((b^2)^(1/2)) == abs(b)
    @eqtest simplify((a^2.0)^(1//2)) == abs(a)
    @eqtest simplify((b^2.0)^(1/2)) == abs(b)

    # log/exp inverses — https://github.com/JuliaSymbolics/SymbolicUtils.jl/issues/1047
    @eqtest simplify(log(exp(a))) == a
    @eqtest simplify(exp(log(a))) == a
    @syms z  # unrestricted (Number), not Real
    @eqtest simplify(log(exp(z))) == log(exp(z))  # branch cuts: do not cancel
    @eqtest simplify(exp(log(z))) == z

end

@testset "abs rules" begin
    @syms r::Real z  # z unrestricted (Number)

    @eqtest simplify(abs(-r)) == abs(r)
    @eqtest simplify(abs(r)^2) == r^2
    @eqtest simplify(abs(abs(r))) == abs(r)
    @eqtest simplify(sqrt(r^2)) == abs(r)
    @eqtest simplify((r^2)^(1//2)) == abs(r)
    @eqtest simplify(abs(-2 * r)) == abs(2 * r)
    @test unwrap_const(simplify(term(abs, -2))) == 2
    @test unwrap_const(simplify(substitute(abs(z), Dict(z => -2)))) == 2

    # |z|^2 ≠ z^2 for non-real z — do not fold
    @eqtest simplify(abs(z)^2) == abs(z)^2
    # sqrt(z^2) = ±z ≠ |z| for complex z — do not fold either spelling
    @eqtest simplify(sqrt(z^2)) == sqrt(z^2)
    @eqtest simplify((z^2)^(1//2)) == sqrt(z^2)
end

@testset "simplify_fractions" begin
    @syms x y z
    @eqtest unwrap_const(simplify(2 * ((y + z) / x) - 2 * y / x - z / x * 2)) == 0
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

@testset "Threaded simplify with getindex (#856)" begin
    # Threaded Walk must keep the original node when the rewriter returns
    # `nothing` (same as serial); otherwise Const{nothing} breaks getindex rebuilds.
    @syms T[1:2] Ca[1:2] CO3[1:2] Ω[1:2]
    @syms atmtoPa aspₐ bsp csp dsp rsp sal_val pressure
    eq = Ω[2] - (Ca[2] * CO3[2] * exp((-atmtoPa * (aspₐ - bsp * (T[2])) * pressure +
                                        (atmtoPa^2) * (csp - dsp * (T[2])) * (pressure^2)) /
                                       (rsp * (T[2])))) /
                (1.5 * exp(316.9463 + sqrt(sal_val) * (1.6233 + -118.64 / (T[2])) -
                           0.06999 * sal_val - 48.7537 * log((T[2])) + -13348.09 / (T[2])))
    serial = simplify(eq; expand=false, threaded=false)
    threaded = simplify(eq; expand=false, threaded=true, thread_subtree_cutoff=3)
    @eqtest serial == threaded
end

@testset "Threaded Prewalk/Postwalk (#856)" begin
    @syms a b Ω[1:1]
    r = @rule(sin(~x) => cos(~x))
    ex = sin(a) + b * sin(Ω[1])
    for Walk in (Rewriters.Prewalk, Rewriters.Postwalk)
        serial = Walk(r; threaded=false)(ex)
        threaded = Walk(r; threaded=true, thread_cutoff=1)(ex)
        @eqtest serial == threaded
        @eqtest serial == cos(a) + b * cos(Ω[1])
    end
end

_g(y) = sin
@testset "interpolation" begin
    @syms a

    # Computed heads with no slots are evaluated (same as `$`-interpolation).
    @test @rule(_g(1)(a) => 2)(sin(a)) == 2
    @test @rule($(_g(1))(a) => 2)(sin(a)) == 2
end

@testset "where" begin

    @syms a b
    _f(x) = x === a
    r = @rule ~x => ~x where {_f(~x)}
    @eqtest r(a) == a
    @test isnothing(r(b))

    r = @acrule ~x => ~x where {_f(~x)}
    @eqtest r(a) == a
    @test r(b) === nothing
end

@testset "ACRule with fewer args than rule arity" begin
    @syms U A B
    # (-U)^2 builds a single-argument Mul; an arity-2 rule must simply not match it
    single = (-U)^2
    @test length(arguments(single)) == 1
    r = @acrule ~x * ~y => ~x
    @test r(single) === nothing
    # the returned factor follows the term's argument order, which varies
    # across sessions, so only require that it is one of the two factors
    @test any(s -> isequal(r(A * B), s), (A, B))
    # end to end: simplify must not throw, and the value must be preserved
    @test isequal(expand(simplify(single)), U^2)
end
