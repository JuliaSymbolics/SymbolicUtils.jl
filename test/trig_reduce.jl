using SymbolicUtils
using SymbolicUtils: unwrap_const

include("utils.jl")

@testset "trig_reduce: product-to-sum (circular)" begin
    @syms A B

    @eqtest trig_reduce(cos(A) * cos(B)) == (1//2)*(cos(A - B) + cos(A + B))
    @eqtest trig_reduce(sin(A) * sin(B)) == (1//2)*cos(A - B) - (1//2)*cos(A + B)
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

    @eqtest trig_reduce(2 * cos(A) * cos(B)) == cos(A - B) + cos(A + B)
    @eqtest trig_reduce(r * cos(x)^2) == (1//2)*r + (1//2)*cos(2x)*r
end

@testset "trig_reduce: mixed products" begin
    @syms x

    @eqtest trig_reduce(cos(x) * cos(3x)) == (1//2)*(cos(2x) + cos(4x))
    @eqtest trig_reduce(sin(x) * cos(x)) == (1//2)*sin(2x)
end

@testset "trig_reduce: product-to-sum (hyperbolic)" begin
    @syms A B

    result_cc = trig_reduce(cosh(A) * cosh(B))
    @eqtest result_cc == (1//2)*(cosh(A - B) + cosh(A + B))

    result_ss = trig_reduce(sinh(A) * sinh(B))
    @eqtest result_ss == (1//2)*cosh(A + B) - (1//2)*cosh(A - B)

    result_sc = trig_reduce(sinh(A) * cosh(B))
    @eqtest result_sc == (1//2)*(sinh(A + B) + sinh(A - B))
end

@testset "trig_reduce: power reduction (hyperbolic)" begin
    @syms x

    @eqtest trig_reduce(cosh(x)^2) == (1//2) + (1//2)*cosh(2x)
    @eqtest trig_reduce(sinh(x)^2) == (1//2)*cosh(2x) - (1//2)
end

@testset "trig_reduce: tan/cot power reduction" begin
    @syms x

    @eqtest trig_reduce(tan(x)^2) == -1 + sec(x)^2
    @eqtest trig_reduce(cot(x)^2) == -1 + csc(x)^2
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
    @syms x

    @eqtest simplify(cos(x)^2; trig_reduce=true) == trig_reduce(cos(x)^2)
    @eqtest simplify(sin(x) * cos(x); trig_reduce=true) == trig_reduce(sin(x) * cos(x))
end

@testset "trig_reduce: non-trig passthrough" begin
    @syms a b c

    @eqtest trig_reduce(a + b + c) == a + b + c
    @eqtest trig_reduce(a * b) == a * b
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
    result = trig_reduce(cos(x)*cos(y) + sin(x)*sin(y))
    @eqtest result == cos(x - y)

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
end
