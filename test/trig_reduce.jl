using SymbolicUtils
using SymbolicUtils: unwrap_const

include("utils.jl")

@testset "trig_reduce: product-to-sum (circular)" begin
    @syms A B

    # cos(A-B) vs cos(-A+B) are isequal-distinct but mathematically identical;
    # which one trig_reduce produces depends on ACDict's (non-deterministic)
    # iteration order, so accept either.
    result_cc = trig_reduce(cos(A) * cos(B))
    @test isequal(result_cc, (1//2)*(cos(A - B) + cos(A + B))) ||
          isequal(result_cc, (1//2)*(cos(-A + B) + cos(A + B)))

    result_ss = trig_reduce(sin(A) * sin(B))
    @test isequal(result_ss, (1//2)*cos(A - B) - (1//2)*cos(A + B)) ||
          isequal(result_ss, (1//2)*cos(-A + B) - (1//2)*cos(A + B))

    @eqtest trig_reduce(sin(A) * cos(B)) == (1//2)*(sin(A + B) + sin(A - B))
    # Commutativity
    @eqtest trig_reduce(cos(B) * sin(A)) == (1//2)*(sin(A + B) + sin(A - B))
end

@testset "trig_reduce: power reduction (circular)" begin
    @syms x

    @eqtest trig_reduce(cos(x)^2) == (1//2) + (1//2)*cos(2x)
    @eqtest trig_reduce(sin(x)^2) == (1//2) - (1//2)*cos(2x)
    @eqtest trig_reduce(cos(x)^3) == (1//4)*cos(3x) + (3//4)*cos(x)
    @eqtest trig_reduce(sin(x)^3) == -(1//4)*sin(3x) + (3//4)*sin(x)
end

@testset "trig_reduce: with coefficients" begin
    @syms A B r x

    # cos(A-B) vs cos(-A+B): see note in "product-to-sum (circular)" testset.
    result = trig_reduce(2 * cos(A) * cos(B))
    @test isequal(result, cos(A - B) + cos(A + B)) ||
          isequal(result, cos(-A + B) + cos(A + B))
    @eqtest trig_reduce(r * cos(x)^2) == (1//2)*r + (1//2)*cos(2x)*r
end

@testset "trig_reduce: mixed products" begin
    @syms x

    @eqtest trig_reduce(cos(x) * cos(3x)) == (1//2)*(cos(2x) + cos(4x))
    @eqtest trig_reduce(sin(x) * cos(x)) == (1//2)*sin(2x)
end

@testset "trig_reduce: product-to-sum (hyperbolic)" begin
    @syms A B

    # cosh(A-B) vs cosh(-A+B): see note in "product-to-sum (circular)" testset.
    result_cc = trig_reduce(cosh(A) * cosh(B))
    @test isequal(result_cc, (1//2)*(cosh(A - B) + cosh(A + B))) ||
          isequal(result_cc, (1//2)*(cosh(-A + B) + cosh(A + B)))

    result_ss = trig_reduce(sinh(A) * sinh(B))
    @test isequal(result_ss, (1//2)*cosh(A + B) - (1//2)*cosh(A - B)) ||
          isequal(result_ss, (1//2)*cosh(A + B) - (1//2)*cosh(-A + B))

    result_sc = trig_reduce(sinh(A) * cosh(B))
    @eqtest result_sc == (1//2)*(sinh(A + B) + sinh(A - B))
    # Commutativity
    @eqtest trig_reduce(cosh(B) * sinh(A)) == (1//2)*(sinh(A + B) + sinh(A - B))
end

@testset "trig_reduce: power reduction (hyperbolic)" begin
    @syms x

    @eqtest trig_reduce(cosh(x)^2) == (1//2) + (1//2)*cosh(2x)
    @eqtest trig_reduce(sinh(x)^2) == (1//2)*cosh(2x) - (1//2)
end

@testset "trig_reduce: tan/cot power reduction" begin
    @syms x
    using SymbolicUtils: unwrap_const

    # tan/cot now reduce to sin/cos form via half-angle identities:
    # tan(x)^2 = (1 - cos(2x)) / (1 + cos(2x))
    # cot(x)^2 = (1 + cos(2x)) / (1 - cos(2x))
    r_tan2 = trig_reduce(tan(x)^2)
    @test abs(Float64(unwrap_const(substitute(r_tan2, Dict(x => 0.7); fold=Val(true)))) - tan(0.7)^2) < 1e-12
    # Should contain no remaining tan/sec
    @test !occursin("tan", string(r_tan2))
    @test !occursin("sec", string(r_tan2))

    r_cot2 = trig_reduce(cot(x)^2)
    @test abs(Float64(unwrap_const(substitute(r_cot2, Dict(x => 0.7); fold=Val(true)))) - cot(0.7)^2) < 1e-12
    @test !occursin("cot", string(r_cot2))
    @test !occursin("csc", string(r_cot2))
end

@testset "trig_reduce: exponential rules" begin
    @syms a b

    @eqtest trig_reduce(exp(a) * exp(b)) == exp(a + b)
    @eqtest trig_reduce(exp(a)^2) == exp(2a)
end

@testset "trig_reduce: does not change default simplify" begin
    @syms x y

    @test unwrap_const(simplify(sin(x)^2 + cos(x)^2)) == 1
    @test unwrap_const(simplify(cos(x)^2 + 1 + sin(x)^2)) == 2
    @eqtest simplify(cos(x)^2) == cos(x)^2
    @eqtest simplify(2cos(x) * sin(x)) == sin(2x)
end

@testset "trig_reduce via simplify kwarg" begin
    @syms x θ φ

    # trig_reduce=true reduces all
    @eqtest simplify(cos(x)^2; trig_reduce=true) == trig_reduce(cos(x)^2)
    @eqtest simplify(sin(x) * cos(x); trig_reduce=true) == trig_reduce(sin(x) * cos(x))

    # trig_reduce=[θ] reduces only trig in θ
    @eqtest simplify(cos(θ)^2; trig_reduce=[θ]) == (1//2) + (1//2)*cos(2θ)
    @eqtest simplify(cos(x)^2; trig_reduce=[θ]) == cos(x)^2

    # trig_reduce=θ (single symbol, not vector)
    @eqtest simplify(cos(θ)^2; trig_reduce=θ) == (1//2) + (1//2)*cos(2θ)

    # multi-variable expression: cos(θ)^2 * cos(φ)^2, reduce only in θ
    result = simplify(cos(θ)^2 * cos(φ)^2; trig_reduce=[θ])
    # cos(θ)^2 should reduce, cos(φ)^2 should stay
    @test abs(Float64(unwrap_const(substitute(result, Dict(θ => 0.5, φ => 1.0); fold=Val(true)))) - cos(0.5)^2*cos(1.0)^2) < 1e-12
    # verify cos(φ)^2 survived
    @test occursin("cos(φ)^2", string(result))

    # multi-variable expression: reduce in both θ and φ
    result2 = simplify(cos(θ)^2 * cos(φ)^2; trig_reduce=[θ, φ])
    # both should reduce
    @test !occursin("cos(θ)^2", string(result2))
    @test !occursin("cos(φ)^2", string(result2))
    @test abs(Float64(unwrap_const(substitute(result2, Dict(θ => 0.5, φ => 1.0); fold=Val(true)))) - cos(0.5)^2*cos(1.0)^2) < 1e-12
end

@testset "trig_reduce: non-trig passthrough" begin
    @syms a b c x

    @eqtest trig_reduce(a + b + c) == a + b + c
    @eqtest trig_reduce(a * b) == a * b

    # Bare symbol (not a call): tests the !iscall early exit
    @eqtest trig_reduce(x) == x
end

@testset "Prefactor factoring (PR #1089 regression)" begin
    @syms x y

    @test unwrap_const(simplify(3 * sin(y)^2 + 3 * cos(y)^2)) == 3
end

# Numerical verification uses the standard SymbolicUtils pattern:
#   unwrap_const(substitute(expr, Dict(...); fold=Val(true)))

@testset "trig_reduce: higher powers (numerical)" begin
    @syms x

    # cos(x)^4
    r4 = trig_reduce(cos(x)^4)
    @test abs(Float64(unwrap_const(substitute(r4, Dict(x => 1.0); fold=Val(true)))) - cos(1.0)^4) < 1e-12

    # cos(x)^5
    r5 = trig_reduce(cos(x)^5)
    @test abs(Float64(unwrap_const(substitute(r5, Dict(x => 0.7); fold=Val(true)))) - cos(0.7)^5) < 1e-12

    # sin(x)^4
    s4 = trig_reduce(sin(x)^4)
    @test abs(Float64(unwrap_const(substitute(s4, Dict(x => 1.3); fold=Val(true)))) - sin(1.3)^4) < 1e-12

    # sin(x)^6
    s6 = trig_reduce(sin(x)^6)
    @test abs(Float64(unwrap_const(substitute(s6, Dict(x => 2.1); fold=Val(true)))) - sin(2.1)^6) < 1e-12

    # cos(x)^8
    r8 = trig_reduce(cos(x)^8)
    @test abs(Float64(unwrap_const(substitute(r8, Dict(x => 0.9); fold=Val(true)))) - cos(0.9)^8) < 1e-12
end

@testset "trig_reduce: same-argument products" begin
    @syms x

    # sin(x)*sin(x) should give same as sin(x)^2
    @eqtest trig_reduce(sin(x) * sin(x)) == trig_reduce(sin(x)^2)

    # cos(x)*cos(x) should give same as cos(x)^2
    @eqtest trig_reduce(cos(x) * cos(x)) == trig_reduce(cos(x)^2)
end

@testset "trig_reduce: nested trig (sin of cos etc)" begin
    @syms x

    # sin(cos(x))^2 — should still power-reduce the outer sin^2
    result = trig_reduce(sin(cos(x))^2)
    @eqtest result == (1//2) - (1//2)*cos(2*cos(x))

    # cos(sin(x)) * cos(sin(x)) — product of same nested trig
    result2 = trig_reduce(cos(sin(x)) * cos(sin(x)))
    @eqtest result2 == (1//2) + (1//2)*cos(2*sin(x))
end

@testset "trig_reduce: compound arguments (numerical)" begin
    @syms a b x

    # cos(a+b) * cos(a-b)
    result = trig_reduce(cos(a + b) * cos(a - b))
    @test abs(Float64(unwrap_const(substitute(result, Dict(a => 1.0, b => 0.5); fold=Val(true)))) - cos(1.5)*cos(0.5)) < 1e-12

    # sin(2x) * cos(3x)
    result2 = trig_reduce(sin(2x) * cos(3x))
    @test abs(Float64(unwrap_const(substitute(result2, Dict(x => 1.2); fold=Val(true)))) - sin(2.4)*cos(3.6)) < 1e-12

    # cos(x)^2 * sin(x)^2 — should give (1 - cos(4x))/8
    result3 = trig_reduce(cos(x)^2 * sin(x)^2)
    @test abs(Float64(unwrap_const(substitute(result3, Dict(x => 0.8); fold=Val(true)))) - cos(0.8)^2*sin(0.8)^2) < 1e-12
end

@testset "trig_reduce: zero and identity expressions" begin
    @syms x

    # sin(x)^2 + cos(x)^2 after trig_reduce should simplify to 1
    # (expand both, cos(2x) terms cancel)
    result = trig_reduce(sin(x)^2 + cos(x)^2)
    @test unwrap_const(result) == 1

    # Pure number should pass through
    @test unwrap_const(trig_reduce(42)) == 42

    # Single trig term (no reduction needed)
    @eqtest trig_reduce(sin(x)) == sin(x)
    @eqtest trig_reduce(cos(x)) == cos(x)
end

@testset "trig_reduce: multiple variables (numerical)" begin
    @syms x y z

    # cos(x)*cos(y) + sin(x)*sin(y) → should equal cos(x-y)
    # cos(x-y) vs cos(-x+y): see note in "product-to-sum (circular)" testset.
    result = trig_reduce(cos(x)*cos(y) + sin(x)*sin(y))
    @test isequal(result, cos(x - y)) || isequal(result, cos(-x + y))

    # Three-variable product: cos(x)*cos(y)*cos(z) — should fully linearize
    result3 = trig_reduce(cos(x)*cos(y)*cos(z))
    @test abs(Float64(unwrap_const(substitute(result3, Dict(x => 0.3, y => 0.7, z => 1.1); fold=Val(true)))) - cos(0.3)*cos(0.7)*cos(1.1)) < 1e-12
end

@testset "trig_reduce: hyperbolic (numerical)" begin
    @syms x y

    # cosh(x)^2
    r1 = trig_reduce(cosh(x)^2)
    @test abs(Float64(unwrap_const(substitute(r1, Dict(x => 1.5); fold=Val(true)))) - cosh(1.5)^2) < 1e-12

    # sinh(x)*cosh(x)
    r2 = trig_reduce(sinh(x)*cosh(x))
    @test abs(Float64(unwrap_const(substitute(r2, Dict(x => 0.8); fold=Val(true)))) - sinh(0.8)*cosh(0.8)) < 1e-12

    # sinh(x)*sinh(y)
    r3 = trig_reduce(sinh(x)*sinh(y))
    @test abs(Float64(unwrap_const(substitute(r3, Dict(x => 1.0, y => 0.5); fold=Val(true)))) - sinh(1.0)*sinh(0.5)) < 1e-12

    # cosh(x)^3 — higher power
    r4 = trig_reduce(cosh(x)^3)
    @test abs(Float64(unwrap_const(substitute(r4, Dict(x => 0.6); fold=Val(true)))) - cosh(0.6)^3) < 1e-12

    # sinh(x)^4
    r5 = trig_reduce(sinh(x)^4)
    @test abs(Float64(unwrap_const(substitute(r5, Dict(x => 0.9); fold=Val(true)))) - sinh(0.9)^4) < 1e-12
end

@testset "trig_reduce: vars kwarg (variable-targeted reduction)" begin
    @syms r θ x y

    # Only reduce trig of θ, not x
    # r^3 * cos(θ)^3 with vars=[θ] should reduce cos(θ)^3 but keep r^3
    result = trig_reduce(r^3 * cos(θ)^3; vars=[θ])
    @test abs(Float64(unwrap_const(substitute(result, Dict(r => 2.0, θ => 0.5); fold=Val(true)))) - 2.0^3*cos(0.5)^3) < 1e-12

    # cos(θ)^2 should reduce when vars=[θ]
    @eqtest trig_reduce(cos(θ)^2; vars=[θ]) == (1//2) + (1//2)*cos(2θ)

    # cos(x)^2 should NOT reduce when vars=[θ] (x not in target vars)
    @eqtest trig_reduce(cos(x)^2; vars=[θ]) == cos(x)^2

    # Mixed: cos(θ)^2 * cos(x)^2 with vars=[θ] reduces only the θ part
    result2 = trig_reduce(cos(θ)^2 * cos(x)^2; vars=[θ])
    # cos(θ)^2 → (1+cos(2θ))/2, cos(x)^2 stays
    @test abs(Float64(unwrap_const(substitute(result2, Dict(θ => 0.5, x => 1.0); fold=Val(true)))) - cos(0.5)^2*cos(1.0)^2) < 1e-12
    # Verify cos(x)^2 survived unreduced
    has_cos_x_sq = occursin("cos(x)^2", string(result2)) || occursin("cos(x)^2", string(simplify(result2)))
    @test has_cos_x_sq

    # vars as single symbol (not vector)
    @eqtest trig_reduce(cos(θ)^2; vars=θ) == (1//2) + (1//2)*cos(2θ)

    # vars=nothing (default) reduces everything
    @eqtest trig_reduce(cos(x)^2; vars=nothing) == (1//2) + (1//2)*cos(2x)

    # vars=[] (empty vector) reduces nothing — no target variables means no
    # guarded rules fire, so the expression is returned unchanged.
    @eqtest trig_reduce(cos(x)^2; vars=Symbol[]) == cos(x)^2
end

@testset "trig_reduce: interaction with simplify_fractions" begin
    @syms x

    # trig in a fraction: sin(x)^2 / cos(x) — should reduce numerator
    result = trig_reduce(sin(x)^2 / cos(x))
    @test abs(Float64(unwrap_const(substitute(result, Dict(x => 0.7); fold=Val(true)))) - sin(0.7)^2/cos(0.7)) < 1e-12

    # simplify with both trig_reduce and simplify_fractions
    result2 = simplify(sin(x)^2 / cos(x); trig_reduce=true, simplify_fractions=true)
    @test abs(Float64(unwrap_const(substitute(result2, Dict(x => 0.7); fold=Val(true)))) - sin(0.7)^2/cos(0.7)) < 1e-12
end

@testset "_has_neg_leading / _is_neg_term: corner cases" begin
    import SymbolicUtils: _has_neg_leading, _is_neg_term, unwrap
    @syms A::Real B::Real C::Real

    # -- Majority vote: ADD with a clear (non-tied) majority --

    # coeff=-2 (negative), A (positive), B (negative, since term is -B):
    # 2 negative vs 1 positive -> negative
    @test _has_neg_leading(unwrap(-2 + A - B)) == true

    # A (positive), B (negative, since term is -B), C (positive):
    # 2 positive vs 1 negative -> not negative
    @test _has_neg_leading(unwrap(A - B + C)) == false

    # A (negative, since term is -A), B (negative, since term is -B), C (positive):
    # 2 negative vs 1 positive -> negative
    @test _has_neg_leading(unwrap(-A - B + C)) == true

    # 3 negative, 0 positive: unambiguous majority negative
    @test _has_neg_leading(unwrap(-A - B - C)) == true

    # 3 positive, 0 negative: unambiguous majority positive (not negative)
    @test _has_neg_leading(unwrap(A + B + C)) == false

    # -- Majority vote: exact ties (equal counts) resolve to non-negative --

    # 1 positive (A), 1 negative (-B): tie -> not negative
    @test _has_neg_leading(unwrap(A - B)) == false
    @test _has_neg_leading(unwrap(-A + B)) == false

    # coeff=-1 (negative), A (positive), B (negative), C (positive): 2 vs 2 tie
    @test _has_neg_leading(unwrap(-1 + A - B + C)) == false

    # -- MUL case: real coefficient sign (unaffected by the ADD rework) --

    @test _has_neg_leading(unwrap(-3 * A)) == true
    @test _has_neg_leading(unwrap(3 * A)) == false

    # -- MUL case: complex coefficient has no defined sign -> not negative --

    @test _has_neg_leading(unwrap((2 + 3im) * A)) == false
    @test _has_neg_leading(unwrap((-2 - 3im) * A)) == false

    # -- Const / plain number cases --

    @test _has_neg_leading(-5) == true
    @test _has_neg_leading(5) == false
    @test _has_neg_leading(0) == false

    # -- _is_neg_term directly: complex-number sign fallback --

    # Nonzero real part: sign follows the real part
    @test _is_neg_term(3 + 2im) == false
    @test _is_neg_term(-3 + 2im) == true
    @test _is_neg_term(-3 - 2im) == true

    # Zero real part: sign follows the imaginary part
    @test _is_neg_term(0 + 2im) == false
    @test _is_neg_term(0 - 2im) == true

    # Zero (both parts): not negative
    @test _is_neg_term(0 + 0im) == false

    # Real numbers (int, float, rational)
    @test _is_neg_term(-1) == true
    @test _is_neg_term(1) == false
    @test _is_neg_term(0) == false
    @test _is_neg_term(-1.5) == true
    @test _is_neg_term(-1//2) == true
    @test _is_neg_term(1//2) == false

    # Non-numeric input (e.g. a bare symbol) has no defined sign -> false
    @test _is_neg_term(unwrap(A)) == false
end

@testset "trig_reduce: corner cases (zero, large n, mixed sign)" begin
    @syms x y

    # Negative-literal argument normalization
    @eqtest trig_reduce(cos(-x)) == cos(x)
    @eqtest trig_reduce(sin(-x)) == -sin(x)
    @eqtest trig_reduce(cosh(-x)) == cosh(x)
    @eqtest trig_reduce(sinh(-x)) == -sinh(x)

    # Negative coefficient products: cos(-x)*cos(y) should normalize before
    # applying product-to-sum (either structural tie form accepted)
    result = trig_reduce(cos(-x) * cos(y))
    expected1 = (1//2)*(cos(x - y) + cos(x + y))
    expected2 = (1//2)*(cos(-x + y) + cos(x + y))
    @test isequal(result, expected1) || isequal(result, expected2)

    # Negative argument on both sides of a product cancels out
    @eqtest trig_reduce(sin(-x) * sin(-y)) == trig_reduce(sin(x) * sin(y))

    # Odd power with negative argument: sin(-x)^3 reduces to the correct sign
    r3 = trig_reduce(sin(-x)^3)
    @test abs(Float64(unwrap_const(substitute(r3, Dict(x => 0.4); fold=Val(true)))) - sin(-0.4)^3) < 1e-12

    # Larger even/odd powers remain numerically correct
    r10 = trig_reduce(cos(x)^10)
    @test abs(Float64(unwrap_const(substitute(r10, Dict(x => 0.3); fold=Val(true)))) - cos(0.3)^10) < 1e-10

    r11 = trig_reduce(sin(x)^11)
    @test abs(Float64(unwrap_const(substitute(r11, Dict(x => 0.3); fold=Val(true)))) - sin(0.3)^11) < 1e-10

    # trig_reduce on an expression with no trig at all is a no-op
    @eqtest trig_reduce(x^2 + 2x + 1) == x^2 + 2x + 1

    # trig_reduce with maxiters=0 returns the input unchanged
    @eqtest trig_reduce(cos(x)^2; maxiters=0) == cos(x)^2
end

@testset "trig_reduce: trig identities" begin
    @syms x::Real y::Real a::Real b::Real c::Real d::Real

    # cos²(x) - sin²(x) = cos(2x)
    @eqtest trig_reduce(cos(x)^2 - sin(x)^2) == cos(2x)

    # cosh²(x) - sinh²(x) = 1
    @test unwrap_const(trig_reduce(cosh(x)^2 - sinh(x)^2)) == 1

    # sinh(x)*cosh(x) = sinh(2x)/2
    @eqtest trig_reduce(sinh(x)*cosh(x)) == (1//2)*sinh(2x)

    # exp(x)*exp(-x) = 1
    @test Float64(unwrap_const(trig_reduce(exp(x)*exp(-x)))) == 1.0

    # sin²(x)*cos(x) fully linearises (no remaining powers)
    r_ssc = trig_reduce(sin(x)^2 * cos(x))
    @test abs(Float64(unwrap_const(substitute(r_ssc, Dict(x => 0.7); fold=Val(true)))) - sin(0.7)^2*cos(0.7)) < 1e-12
    @test !occursin("^", string(r_ssc))

    # tan(x)^4 fully reduces to cos multi-angle ratios
    r_tan4 = trig_reduce(tan(x)^4)
    @test abs(Float64(unwrap_const(substitute(r_tan4, Dict(x => 0.7); fold=Val(true)))) - tan(0.7)^4) < 1e-12
    @test !occursin("tan", string(r_tan4))

    # Mixed circular/hyperbolic: no identity applies, should be a no-op
    @eqtest trig_reduce(cos(x) * cosh(y)) == cos(x) * cosh(y)

    # Four-cosine product: full linearisation to 8 cosine terms
    r4cos = trig_reduce(cos(a)*cos(b)*cos(c)*cos(d))
    @test abs(Float64(unwrap_const(substitute(r4cos, Dict(a => 0.3, b => 0.5, c => 0.8, d => 1.1); fold=Val(true)))) - cos(0.3)*cos(0.5)*cos(0.8)*cos(1.1)) < 1e-12
    @test !occursin("^", string(r4cos))
    @test !occursin("cos(a)*cos", string(r4cos))
end


@testset "trig_reduce: conversions and cancellations (structural)" begin
    import SymbolicUtils: _iszero
    @syms x::Real y::Real

    # Bare functions stay as-is (matching Mathematica's TrigReduce behavior)
    @eqtest trig_reduce(tan(x)) == tan(x)
    @eqtest trig_reduce(cot(x)) == cot(x)
    @eqtest trig_reduce(sec(x)) == sec(x)
    @eqtest trig_reduce(csc(x)) == csc(x)
    @eqtest trig_reduce(tanh(x)) == tanh(x)
    @eqtest trig_reduce(coth(x)) == coth(x)
    @eqtest trig_reduce(sech(x)) == sech(x)
    @eqtest trig_reduce(csch(x)) == csch(x)

    # Negative argument normalization preserves function type
    @eqtest trig_reduce(tan(-x)) == -tan(x)
    @eqtest trig_reduce(sec(-x)) == sec(x)
    @eqtest trig_reduce(csc(-x)) == -csc(x)
    @eqtest trig_reduce(cot(-x)) == -cot(x)
    @eqtest trig_reduce(tanh(-x)) == -tanh(x)

    # Power reduction to cos/cosh multi-angle ratios
    @eqtest trig_reduce(tan(x)^2) == (1 - cos(2x)) / (1 + cos(2x))
    @eqtest trig_reduce(cot(x)^2) == (1 + cos(2x)) / (1 - cos(2x))
    @eqtest trig_reduce(sec(x)^2) == 2 / (1 + cos(2x))
    @eqtest trig_reduce(csc(x)^2) == 2 / (1 - cos(2x))
    @eqtest trig_reduce(tanh(x)^2) == (-1 + cosh(2x)) / (1 + cosh(2x))

    # Zero folding
    @test _iszero(trig_reduce(tan(0 * x)))
    @test _iszero(trig_reduce(tanh(0 * x)))

    # Period / half-period reduction
    @eqtest trig_reduce(sin(x + 2π)) == sin(x)
    @eqtest trig_reduce(cos(x + 2π)) == cos(x)
    @eqtest trig_reduce(sin(x + π)) == -sin(x)
    @eqtest trig_reduce(cos(x + π)) == -cos(x)
    @eqtest trig_reduce(sin(x + 4π)) == sin(x)
    @eqtest trig_reduce(sin(x + 3π)) == -sin(x)
    @eqtest trig_reduce(tan(x + π)) == tan(x)
    @eqtest trig_reduce(tan(x + 2π)) == tan(x)
    @eqtest trig_reduce(sec(x + π)) == -sec(x)

    # Same-argument cancellation in products
    @eqtest trig_reduce(tan(x) * cos(x)) == sin(x)
    @eqtest trig_reduce(cot(x) * sin(x)) == cos(x)
    @test unwrap_const(trig_reduce(sec(x) * cos(x))) == 1
    @test unwrap_const(trig_reduce(csc(x) * sin(x))) == 1
    @test unwrap_const(trig_reduce(tan(x) * cot(x))) == 1
    @eqtest trig_reduce(sec(x) * sin(x)) == tan(x)
    @eqtest trig_reduce(csc(x) * cos(x)) == cot(x)
    @eqtest trig_reduce(tan(x) * csc(x)) == sec(x)

    # Scalar * bare function stays as-is
    @eqtest trig_reduce(3 * tan(x)) == 3tan(x)

    # Nested: bare function of trig stays
    @eqtest trig_reduce(tan(sin(x))) == tan(sin(x))

    # Dual-conversion: products of two non-sin/cos functions
    r_ts = trig_reduce(tan(x) * sec(x))
    @test abs(Float64(unwrap_const(substitute(r_ts, Dict(x => 0.7); fold=Val(true)))) - tan(0.7)*sec(0.7)) < 1e-12
    @test !occursin("tan", string(r_ts)) && !occursin("sec", string(r_ts))

    r_sc = trig_reduce(sec(x) * csc(x))
    @test abs(Float64(unwrap_const(substitute(r_sc, Dict(x => 0.7); fold=Val(true)))) - sec(0.7)*csc(0.7)) < 1e-12

    # Two-variable: sec(x)*sec(y) fully reduces
    r_ss = trig_reduce(sec(x) * sec(y))
    @test abs(Float64(unwrap_const(substitute(r_ss, Dict(x => 0.3, y => 0.7); fold=Val(true)))) - sec(0.3)*sec(0.7)) < 1e-12
    @test !occursin("sec", string(r_ss))
end

@testset "trig_reduce: compound operations" begin
    @syms x::Real y::Real θ::Real φ::Real

    # -- Mixed products: fallback converts tan/cot/sec/csc to sin/cos,
    #    then product-to-sum + simplify_fractions linearises the result.

    # tan(x)*cos(2x) = sin(x)*cos(2x)/cos(x) = (sin(3x)-sin(x))/(2cos(x))
    r_tc = trig_reduce(tan(x) * cos(2x))
    @test abs(Float64(unwrap_const(substitute(r_tc, Dict(x => 0.7); fold=Val(true)))) - tan(0.7)*cos(1.4)) < 1e-12
    @test !occursin("tan", string(r_tc))

    # cot(x)*sin(3x) = cos(x)*sin(3x)/sin(x) = (sin(2x)+sin(4x))/(2sin(x))
    r_cs = trig_reduce(cot(x) * sin(3x))
    @test abs(Float64(unwrap_const(substitute(r_cs, Dict(x => 0.7); fold=Val(true)))) - cot(0.7)*sin(2.1)) < 1e-12
    @test !occursin("cot", string(r_cs))

    # -- Period reduction in compound expressions --

    # cos(x+π)^2 = (-cos(x))^2 = cos(x)^2 → (1+cos(2x))/2
    @eqtest trig_reduce(cos(x + π)^2) == trig_reduce(cos(x)^2)

    # sin(x+2π)*cos(x) = sin(x)*cos(x) → sin(2x)/2
    @eqtest trig_reduce(sin(x + 2π) * cos(x)) == trig_reduce(sin(x) * cos(x))

    # tan(x+π) = tan(x) (period π)
    @eqtest trig_reduce(tan(x + π)) == trig_reduce(tan(x))

    # -- expand then trig_reduce --

    # (cos(x)+sin(x))^2 → expand → cos²+2cos·sin+sin² → trig_reduce → 1+sin(2x)
    @eqtest trig_reduce(expand((cos(x) + sin(x))^2)) == 1 + sin(2x)

    # -- trig_reduce vs simplify(; trig_reduce=true) produce same result --
    @eqtest trig_reduce(tan(x)^2 + 1) == (2//1) / (1 + cos(2x))
    @eqtest simplify(tan(x)^2 + 1; trig_reduce=true) == (2//1) / (1 + cos(2x))
end

@testset "trig_reduce: multi-variable independence" begin
    @syms x::Real θ::Real φ::Real r::Real

    # vars=[θ]: only θ-dependent trig reduces
    # tan(θ)*cos(φ)^2: tan→sin/cos for θ, cos(φ)^2 survives
    r1 = trig_reduce(tan(θ) * cos(φ)^2; vars=[θ])
    @test !occursin("tan", string(r1))
    @test occursin("cos(φ)^2", string(r1))
    @test abs(Float64(unwrap_const(substitute(r1, Dict(θ => 0.5, φ => 1.0); fold=Val(true)))) - tan(0.5)*cos(1.0)^2) < 1e-12

    # vars=[φ]: cos(φ)^2 reduces, tan(θ) survives
    r2 = trig_reduce(tan(θ) * cos(φ)^2; vars=[φ])
    @test occursin("tan(θ)", string(r2))
    @test !occursin("cos(φ)^2", string(r2))
    @test abs(Float64(unwrap_const(substitute(r2, Dict(θ => 0.5, φ => 1.0); fold=Val(true)))) - tan(0.5)*cos(1.0)^2) < 1e-12

    # sec(θ)^2, vars=[φ]: θ not in target, stays unreduced
    @eqtest trig_reduce(sec(θ)^2; vars=[φ]) == sec(θ)^2

    # Spherical-coordinate style: r²*sin(θ)²*cos(φ), vars=[θ]
    # sin²→(1-cos2θ)/2 then product-to-sum with cos(φ), r² untouched
    r3 = trig_reduce(r^2 * sin(θ)^2 * cos(φ); vars=[θ])
    @test occursin("r^2", string(r3)) || occursin("r²", string(r3))
    @test occursin("cos(φ)", string(r3))
    @test !occursin("sin(θ)^2", string(r3))
    @test abs(Float64(unwrap_const(substitute(r3, Dict(r => 2.0, θ => 0.5, φ => 1.0); fold=Val(true)))) - 4.0*sin(0.5)^2*cos(1.0)) < 1e-12

    # simplify with trig_reduce=[θ]: mixed var targeting through simplify kwarg
    r4 = simplify(cos(θ)^2 * sec(φ)^2; trig_reduce=[θ])
    @test occursin("sec(φ)", string(r4)) || occursin("sec", string(r4))
    @test !occursin("cos(θ)^2", string(r4))
    @test abs(Float64(unwrap_const(substitute(r4, Dict(θ => 0.5, φ => 1.0); fold=Val(true)))) - cos(0.5)^2*sec(1.0)^2) < 1e-12
end
