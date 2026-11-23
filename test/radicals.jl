using Test, SymbolicUtils
using SymbolicUtils: Const, unwrap_const
using SymbolicUtils.Code: toexpr

C(x) = Const{SymReal}(x)

@testset "symbolic roots and rational powers" begin
    @syms x y z::ComplexF64
    @test isequal(sqrt(x) * sqrt(x), x)
    @test isequal(x / sqrt(x), sqrt(x))
    @test isequal(sqrt(x) / x, 1 / sqrt(x))
    @test isequal(cbrt(x)^3, x)
    @test isequal((x^(1 // 2))^(1 // 2), x^(1 // 4))
    @test isequal(sqrt(x)^(2 // 3), x^(1 // 3))
    @test operation(sqrt(z)) === sqrt
end

@testset "non-integer powers do not distribute over products" begin
    @syms x y
    # sqrt(x*y) is defined for x, y < 0 where sqrt(x)*sqrt(y) is not
    @test !isequal(sqrt(x * y), sqrt(x) * sqrt(y))
    @test isequal(sqrt(x * y)^2, x * y)
    @test isequal((4x)^(1 // 2), 2x^(1 // 2))
    @test isequal((3x)^(1 // 2), sqrt(C(3)) * x^(1 // 2))
end

@testset "numeric radicals" begin
    s3 = sqrt(C(3))
    @test operation(s3) === (^)
    @test isequal(s3, C(3)^(1 // 2))
    @test isequal(C(3) / s3, s3)
    @test isequal(3 / s3, s3)
    @test unwrap_const(s3 * s3) == 3
    @test isequal(1 / s3, (1 // 3) * s3)
    @test isequal(s3 / 3, (1 // 3) * s3)
    @test isequal(sqrt(C(12)), 2 * s3)
    @test unwrap_const(sqrt(C(4))) === 2
    @test unwrap_const(sqrt(C(9 // 4))) === 3 // 2
    @test unwrap_const(cbrt(C(27))) === 3
    @test isequal(cbrt(C(-6)), -cbrt(C(6)))
    @test unwrap_const(cbrt(C(-27))) === -3
    @test isequal(sqrt(C(6)) / sqrt(C(2)), s3)
    @test isequal(sqrt(C(2)) * s3, sqrt(C(6)))
    @test isequal(sqrt(C(7 // 2)), (1 // 2) * sqrt(C(14)))
    @test isequal(C(3)^(3 // 2), 3 * s3)
    @test isequal(C(3)^(-1 // 2), (1 // 3) * s3)
    @test unwrap_const(sqrt(C(3.0))) === sqrt(3.0)
    @test unwrap_const(sqrt(C(0))) == 0
    # no DomainError at construction
    @test operation(sqrt(C(-1))) === sqrt

    @syms x
    @test isequal(6 / (s3 * x), 2 * s3 / x)
    @test isequal((s3 * x) / 3, (1 // 3) * s3 * x)
    @test isequal((s3 * x)^2, 3x^2)
    @test isequal((s3 * x)^2.0, 3.0 * x^2.0)

    @syms w vartype = SafeReal
    ss3 = Const{SafeReal}(3)^(1 // 2)
    @test isequal(3 / ss3, ss3)
    @test isequal(w / ss3, (1 // 3) * ss3 * w)
end

@testset "simplification of root terms" begin
    @syms x
    @test isequal(simplify(term(sqrt, x)), sqrt(x))
    @test isequal(simplify(term(cbrt, x)), cbrt(x))
    @test isequal(simplify(term(sqrt, 12)), 2 * sqrt(C(3)))
    @test unwrap_const(simplify(3 / term(sqrt, 3) - sqrt(C(3)))) == 0
end

@testset "printing" begin
    @syms x y
    @test repr(sqrt(x)) == "sqrt(x)"
    @test repr(x^(1 // 2)) == "sqrt(x)"
    @test repr(cbrt(x + y)) == "cbrt(x + y)"
    @test repr(sqrt(C(3))) == "sqrt(3)"
    @test repr(x^(2 // 3)) == "x^(2//3)"
    @test repr(x^(1 // 3)) == "x^(1//3)"
    @test repr(x^(3 // 2)) == "sqrt(x)^3"
    @test repr(x * x * x^(1 // 2)) == "sqrt(x)^5"
    @test repr((x + y)^(3 // 2)) == "sqrt(x + y)^3"
    @test repr(x^(3 // 2) * y) == "(sqrt(x)^3)*y"
    @test repr(2 * sqrt(C(3))) == "2sqrt(3)"
    @test repr(sqrt(x) * y) == "sqrt(x)*y"
end

@testset "codegen" begin
    @syms x
    @test toexpr(x^(1 // 2)) == :($(^)(x, $(1 // 2)))
    @test toexpr(cbrt(x)) == :($cbrt(x))
    @test toexpr(x^(1 // 3)) == :($(^)(x, $(1 // 3)))
    @test toexpr(x^(3 // 2)) == :($(^)(x, $(3 // 2)))
    @test toexpr(x^(5 // 2)) == :($(^)(x, $(5 // 2)))
    k = eval(toexpr(SymbolicUtils.Code.Func([x], [], (x + 1)^(5 // 2))))
    @test @invokelatest(k(3.0)) ≈ 32.0
    # cbrt(x)^2 must stay defined for negative x
    f = eval(toexpr(SymbolicUtils.Code.Func([x], [], cbrt(x)^2)))
    @test @invokelatest(f(-8.0)) ≈ 4.0
    g = eval(toexpr(SymbolicUtils.Code.Func([x], [], 1 / sqrt(x))))
    @test @invokelatest(g(4.0)) ≈ 0.5
    ir = SymbolicUtils.IRStructure{SymReal}()
    h = eval(SymbolicUtils.Code.fast_toexpr(SymbolicUtils.Code.Func([x], [], cbrt(x)^2 + sqrt(x^2)), ir, Dict{Any, Any}()))
    @test @invokelatest(h(-8.0)) ≈ 12.0
end

@testset "radical regression cases" begin
    @syms x i::Int z::ComplexF64

    @testset "colliding radicands" begin
        a, b, c = sqrt(C(2)), cbrt(C(6)), sqrt(C(3))
        expected = sqrt(6.0) * cbrt(6.0)
        @test eval(toexpr((a * b) * c)) ≈ expected
        @test eval(toexpr((a * c) * b)) ≈ expected
    end

    @testset "symbolic root calls" begin
        @test operation(sqrt(x)) === sqrt
        @test isequal(simplify(term(sqrt, x)), term(sqrt, x))
        @test unwrap_const(substitute(cbrt(x), Dict(x => -8.0); fold = Val(true))) == -2.0
        root_argument = @rule cbrt(~a) => ~a
        @test isequal(root_argument(cbrt(x)), x)
    end

    @testset "large root index" begin
        exponent = 1 // typemax(Int)
        @test eval(toexpr(C(2)^exponent)) == 2^exponent
    end

    for generator in (toexpr, f -> SymbolicUtils.Code.fast_toexpr(f, SymbolicUtils.IRStructure{SymReal}(), Dict{Any, Any}()))
        @testset "runtime powers" begin
            for (var, expr, input, expected) in (
                    (i, i^(5 // 2), Int64(10)^12, 1.0e30),
                    (x, cbrt(cbrt(x)), -512.0, -2.0),
                    (z, z^(1 // 3), -8.0 + 0.0im, (-8.0 + 0.0im)^(1 // 3)),
                    (x, x^((big(typemax(Int)) + 3) // 3), 1.0, 1.0),
                )
                @test begin
                    f = eval(generator(SymbolicUtils.Code.Func([var], [], expr)))
                    @invokelatest(f(input)) ≈ expected
                end
            end
            f = eval(generator(SymbolicUtils.Code.Func([x], [], x^(1 // 3))))
            @test_throws DomainError @invokelatest(f(-8.0))
        end
    end
end
