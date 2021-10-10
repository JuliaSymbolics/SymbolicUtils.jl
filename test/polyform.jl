using SymbolicUtils: PolyForm, Term, symtype
using Test, SymbolicUtils

include("utils.jl")

struct CtxPoly end

@testset "div and polyform" begin
    @syms t x(..) y z
    x = x(t)
    @test repr(PolyForm(x-y)) == "x(t) - y"
    @test repr(x/y*x/z) == "(x(t)^2) / (y*z)"
    x = setmetadata(x, CtxPoly, "meta_1")
    expr = ((x-y+z)*(x+4z+1)) /
                                  (y*(2x - 3y + 3z) +
                                   x*(x + z))
    simp_expr = simplify_fractions(expr)
    @test getmetadata(arguments(simp_expr.den)[2], CtxPoly, nothing) == "meta_1"
    @test repr(simp_expr) == repr(simplify_fractions((1 + x + 4z) / (x + 3.0y)))
    @test simplify_fractions(x/(x+3) + 3/(x+3)) == 1
    @test repr(simplify(simplify_fractions(cos(x)/sin(x) + sin(x)/cos(x)))) == "1 / (cos(x(t))*sin(x(t)))"
end

@testset "expand" begin
    @syms a b c d
    @test expand(a * (b + -1 * c) + -1 * (b * a + -1 * c * a)) == 0
    @eqtest simplify(expand(sin((a+b)^2)^2)) == simplify(sin(a^2+2*(b*a)+b^2)^2)
    @test simplify(expand(sin((a+b)^2)^2 + cos((a+b)^2)^2)) == 1
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
    @test expand(a * b - b * a) == 0

    @syms A::Vector{Real}
    # test that the following works
    expand(Term{Real}(getindex, [A, 3]) - 3)
end

@testset "simplify_fractions with quick-cancel" begin
    @syms x y
    @test simplify_fractions(x/2x) == 1//2
    @test simplify_fractions(2x//x) == 2
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
    @eqtest simplify_fractions(x^2/x^2) == 1
    @eqtest simplify_fractions(3x^2/x^3) == 3/x
    @eqtest simplify_fractions(3*(x^2)*(y^3)/(3*(x^3)*(y^2))) == y/x
    @eqtest simplify_fractions(3*(x^x)/x*y) == 3*(x^x)/x*y
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
