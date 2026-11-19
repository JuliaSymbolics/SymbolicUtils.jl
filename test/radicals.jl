using Test, SymbolicUtils
using SymbolicUtils: Const, unwrap_const
using SymbolicUtils.Code: toexpr

C(x) = Const{SymReal}(x)

@testset "sqrt/cbrt are rational powers" begin
    @syms x y z::ComplexF64
    @test isequal(sqrt(x), x^(1 // 2))
    @test isequal(cbrt(x), x^(1 // 3))
    @test operation(sqrt(x)) === (^)
    @test isequal(sqrt(x) * sqrt(x), x)
    @test isequal(x / sqrt(x), sqrt(x))
    @test isequal(sqrt(x) / x, 1 / sqrt(x))
    @test isequal(cbrt(x)^3, x)
    @test isequal(sqrt(sqrt(x)), x^(1 // 4))
    @test isequal(sqrt(x)^(2 // 3), cbrt(x))
    @test isequal(sqrt(z), z^(1 // 2))
end

@testset "non-integer powers do not distribute over products" begin
    @syms x y
    # sqrt(x*y) is defined for x, y < 0 where sqrt(x)*sqrt(y) is not
    @test !isequal(sqrt(x * y), sqrt(x) * sqrt(y))
    @test isequal(sqrt(x * y)^2, x * y)
    @test isequal(sqrt(4x), 2sqrt(x))
    @test isequal(sqrt(3x), sqrt(C(3)) * sqrt(x))
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
    @test isequal(sqrt(C(6)) / sqrt(C(2)), s3)
    @test isequal(sqrt(C(2)) * s3, sqrt(C(6)))
    @test isequal(sqrt(C(7 // 2)), (1 // 2) * sqrt(C(14)))
    @test isequal(C(3)^(3 // 2), 3 * s3)
    @test isequal(C(3)^(-1 // 2), (1 // 3) * s3)
    @test unwrap_const(sqrt(C(3.0))) === sqrt(3.0)
    @test unwrap_const(sqrt(C(0))) == 0
    # no DomainError at construction
    @test operation(sqrt(C(-1))) === (^)

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

@testset "raw sqrt/cbrt terms canonicalize under simplify" begin
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
    @test repr(x^(3 // 2)) == "sqrt(x)^3"
    @test repr(x * x * sqrt(x)) == "sqrt(x)^5"
    @test repr((x + y)^(3 // 2)) == "sqrt(x + y)^3"
    @test repr(x^(3 // 2) * y) == "(sqrt(x)^3)*y"
    @test repr(2 * sqrt(C(3))) == "2sqrt(3)"
    @test repr(sqrt(x) * y) == "sqrt(x)*y"
end

@testset "codegen" begin
    @syms x
    @test toexpr(x^(1 // 2)) == :($sqrt(x))
    @test toexpr(cbrt(x)) == :($cbrt(x))
    @test toexpr(x^(1 // 3)) == :($cbrt(x))
    @test toexpr(x^(3 // 2)) == :($(*)($sqrt(x), x))
    @test toexpr(x^(5 // 2)) == :($(*)($sqrt(x), $(Base.literal_pow)($(^), x, $Val(2))))
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
