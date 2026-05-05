using SymbolicUtils: Term, symtype, unwrap_const, Add, Mul
using Test, SymbolicUtils

include("utils.jl")

@testset "div and polyform" begin
    @syms x y z
    @test repr(x/y*x/z) == "(x^2) / (y*z)"
    @test repr(simplify_fractions(((x-y+z)*(x+4z+1)) /
                                  (y*(2x - 3y + 3z) +
                                   x*(x + z)))) == repr(simplify_fractions((1 + x + 4z) / (x + 3y)))
    @test unwrap_const(simplify_fractions( (1/x)^2 * x^2)) == 1
    @test unwrap_const(simplify_fractions(x/(x+3) + 3/(x+3))) == 1
    @test repr(simplify(simplify_fractions(cos(x)/sin(x) + sin(x)/cos(x)))) == "2 / sin(2x)"
end

@testset "expand" begin
    @syms a b c d

    @test unwrap_const(expand(term(*, 0, a))) == 0
    @test unwrap_const(expand(a * (b + -1 * c) + -1 * (b * a + -1 * c * a))) == 0
    @eqtest simplify(expand(sin((a+b)^2)^2)) == simplify(sin(a^2+2*(b*a)+b^2)^2)
    @test unwrap_const(simplify(expand(sin((a+b)^2)^2 + cos((a+b)^2)^2))) == 1
    @syms x1::Real f(::Real)::Real

    # issue 193
    #@test isequal(expand(f(2.0 + x1)), f(2.0 + x1))
    @test symtype(expand(f(x1 + 2.0))) == Real

    # cleanup rules
    # I don't think we need this anymore?
   #@test expand(Term{Number}(identity, 0)) == 0
   #@test expand(Term{Number}(one, 0)) == 1
   #@test expand(Term{Number}(zero, 0)) == 0
   #@test expand(identity(a * b) - b * a) == 0
    @test unwrap_const(expand(a * b - b * a)) == 0

    @syms A::Vector{Real}
    # test that the following works
    expand(Term{SymReal}(getindex, [A, 3]; type = Real) - 3)
end

@testset "simplify_fractions with quick-cancel" begin
    @syms x y
    @test unwrap_const(simplify_fractions(x/2x)) == 1//2
    @test unwrap_const(simplify_fractions(2x/x)) == 2
    @eqtest simplify_fractions((x+y) * (x-y) / (x+y)) == (x-y)
    @eqtest simplify_fractions(x^3 * y / x) == y*x^2
    @eqtest simplify_fractions(2x^3 * y / x) == 2y*x^2
    @eqtest simplify_fractions(x / (3(x^3)*y)) == simplify_fractions(1/(3*(y*x^2)))
    @eqtest simplify_fractions(2x / (3(x^3)*y)) == simplify_fractions(2/(3*(y*x^2)))
    @eqtest simplify_fractions(x^2 / (3(x^3)*y)) == simplify_fractions(1/(3*(y*x)))
    @eqtest simplify_fractions((3(x^3)*y) / x^2) == simplify_fractions(3*(y*x))
    @eqtest simplify_fractions(x^2/x^4) == (1/x^2)
    @eqtest simplify_fractions(x^2/x^3) == 1/x
    @eqtest simplify_fractions(x^3/x^2) == x
    @eqtest unwrap_const(simplify_fractions(x^2/x^2)) == 1
    @eqtest simplify_fractions(3x^2/x^3) == 3/x
    @eqtest simplify_fractions(3*(x^2)*(y^3)/(3*(x^3)*(y^2))) == y/x
    @eqtest simplify_fractions(3*(x^x)/x*y) == 3*(x^x)/x*y

    ##404#issuecomment-939404030
    a = 1 / (x - (2//1)) + ((-5//1) - x) / ((x - (2//1))^2)
    @test isequal(simplify_fractions(a), 7/expand(-(x-2)^2))

    # https://github.com/JuliaSymbolics/Symbolics.jl/issues/968
    @eqtest simplify_fractions((x * y + (1//2) * x) / (2 * x)) == (1//2 + y) / 2
end

import DynamicPolynomials as DP
import MultivariatePolynomials as MP
using SymbolicUtils: PolynomialT, poly_to_gcd_form, MonomialOrder

# `to_poly!` returns `PolynomialT = DP.Polynomial{V,M,Number}` — the
# coefficient eltype is the abstract `Number`. The previous broadcast form in
# `poly_to_gcd_form` (`Integer.(coeffs)`, `rationalize.(...)`, `float.(...)`,
# `(complex ∘ float).(...)`) preserved abstractness whenever the underlying
# concrete element types were *heterogeneous* — e.g.
# `Integer.(Number[Int8(1), Int64(-2), Int64(1)])` returns
# `Vector{Signed}` rather than `Vector{Int64}`. The resulting
# `DP.Polynomial` then carried an abstract type parameter
# (`Signed` / `Integer` / `AbstractFloat` / `Real`), and `MP.gcd`'s
# `isolate_variable` crashed downstream with a
# `MethodError(Term{T,M} where T, (::Vector{Term{<:Any, M}},))`.
#
# Guard: each branch of `poly_to_gcd_form` must return a polynomial with a
# *concrete* coefficient type even when the input vector is heterogeneous
# within the relevant numeric kind.
let v = only(DP.@polyvar __PolyToGcdFormTest__ monomial_order = MonomialOrder)
    # CRITICAL: build the coefficient vector with the typed-literal form
    # `Number[Int8(1), Int64(-2), Int64(1)]` rather than going through
    # `Vector{Number}([…])` — the latter passes through an inner untyped
    # literal which `promote_type`-normalises to the LUB element type
    # (collapsing Int8+Int64 down to Int64 before reaching `Vector{Number}`),
    # so the heterogeneity is gone and the bug doesn't reproduce.
    function poly_with_coeffs(coeffs::Vector{Number}, monos_template)
        DP.Polynomial(coeffs, MP.monomials(monos_template))
    end

    @testset "poly_to_gcd_form gives concrete coefficient eltype" begin
        @testset "heterogeneous integer kinds (Int8 + Int64)" begin
            # Pre-fix: `Integer.(Number[Int8(1), Int64(-2), Int64(1)])` →
            # `Vector{Signed}` → polynomial type parameter `Signed` (abstract).
            p = poly_with_coeffs(Number[Int8(1), Int64(-2), Int64(1)],
                                  (1 - v) * (1 - v))   # 1 - 2v + v^2
            @test p isa PolynomialT
            g = poly_to_gcd_form(p)
            T = eltype(MP.coefficients(g))
            @test isconcretetype(T)
            @test T <: Integer
            @test MP.coefficients(g) == [1, -2, 1]
        end

        @testset "heterogeneous rational kinds (Rational{Int8} + Rational{Int64})" begin
            p = poly_with_coeffs(Number[Rational{Int8}(1, 2), Rational{Int64}(-1, 3)],
                                  (1//2 - v))
            g = poly_to_gcd_form(p)
            T = eltype(MP.coefficients(g))
            @test isconcretetype(T)
            @test T <: Rational
        end

        @testset "heterogeneous float kinds (Float32 + Float64)" begin
            p = poly_with_coeffs(Number[Float32(1.5), Float64(-2.5)], (1.5 - v))
            g = poly_to_gcd_form(p)
            T = eltype(MP.coefficients(g))
            @test isconcretetype(T)
            @test T <: AbstractFloat
        end

        @testset "heterogeneous complex kinds (ComplexF32 + ComplexF64)" begin
            p = poly_with_coeffs(Number[ComplexF32(1, 2), ComplexF64(0, 0.5)],
                                  (1.0 + 2.0im - v))
            g = poly_to_gcd_form(p)
            T = eltype(MP.coefficients(g))
            @test isconcretetype(T)
            @test T <: Complex
        end

        @testset "MP.gcd works on heterogeneous-coefficient polynomials" begin
            # On the buggy version this used to throw
            # `MethodError(Term{T,M} where T, (::Vector{Term{<:Any, M}},))`
            # via the `isolate_variable` path inside `multivariate_gcd`.
            p1 = poly_with_coeffs(Number[Int8(1), Int64(-2), Int64(1)],
                                   (1 - v) * (1 - v))     # 1 - 2v + v^2
            p2 = poly_with_coeffs(Number[Int8(1), Int64(-1)],
                                   (1 + v^2))             # 1 + v^2 (template; coeffs replaced)
            g1 = poly_to_gcd_form(p1)
            g2 = poly_to_gcd_form(p2)
            @test gcd(g1, g2) isa DP.Polynomial
        end
    end
end

@testset "simplify_fractions doesn't crash on heterogeneous coefficients" begin
    # End-to-end repro of the crash surfaced via SymbolicIntegration.jl's
    # difficult-test verifier: a `simplify(num/den; expand=true)` whose num/den
    # both go through `to_poly!` → `safe_gcd` → `poly_to_gcd_form`, where
    # heterogeneous coefficient types (e.g. integers in `num` mixed with
    # rationals/floats in `den`) used to send `MP.gcd` into the abstract-eltype
    # `MethodError` path.
    @syms x

    # Mix of integer, rational, and float coefficients across num and den.
    num = (x^4 - x^3 + 2x^2 - x + 2)
    den = (x - 1) * (x^2 + 2)^2
    @test simplify_fractions(num / den) isa Any   # just must not throw

    # Float ↔ rational mix.
    @test simplify_fractions((1.0 + 0.5*x - x^2) / ((1//2)*x^2 - 1)) isa Any
end

@testset "isone iszero" begin
    @syms a b c d e f g h i
    x = (f + ((((g*(c^2)*(e^2)) / d - e*h*(c^2)) / b + (-c*e*f*g) / d + c*e*i) /
              (i + ((c*e*g) / d - c*h) / b + (-f*g) / d) - c*e) / b +
         ((g*(f^2)) / d + ((-c*e*f*g) / d + c*f*h) / b - f*i) /
         (i + ((c*e*g) / d - c*h) / b + (-f*g) / d)) / d

    o = (d + (e*((c*(g + (-d*g) / d)) / (i + (-c*(h + (-e*g) / d)) / b + (-f*g) / d))) / b + (-f*(g + (-d*g) / d)) / (i + (-c*(h + (-e*g) / d)) / b + (-f*g) / d)) / d
    @test SymbolicUtils.fraction_iszero(x)
    @test !SymbolicUtils.fraction_isone(x)
    @test SymbolicUtils.fraction_isone(o)
end
