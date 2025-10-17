using SymbolicUtils
using SymbolicUtils: Sym, Term, symtype, BasicSymbolic, Const, ArgsT, promote_symtype, promote_shape, ShapeVecT, Unknown
using Test
import NaNMath
import LinearAlgebra
import SpecialFunctions: besselj, bessely, besseli, besselk, polygamma, beta, logbeta, hankelh1, hankelh2, expint, gamma, erf

@testset "promote_symtype with BigInt" begin
    # promote_symtype with BigInt combinations
    @test promote_symtype(+, BigInt, BigInt) == BigInt
    @test promote_symtype(+, BigInt, Int) == promote_type(Int, Integer)
    @test promote_symtype(+, Int, BigInt) == promote_type(Int, Integer)
    @test promote_symtype(-, BigInt, BigInt) == BigInt
    @test promote_symtype(*, BigInt, BigInt) == BigInt
    @test promote_symtype(^, BigInt, BigInt) == BigInt
    @test promote_symtype(max, BigInt, BigInt) == BigInt
    @test promote_symtype(min, BigInt, BigInt) == BigInt
end

@testset "promote_symtype with BigFloat" begin
    # promote_symtype with BigFloat combinations
    @test promote_symtype(+, BigFloat, BigFloat) == BigFloat
    @test promote_symtype(+, BigFloat, Int) == promote_type(Int, Real)
    @test promote_symtype(+, Int, BigFloat) == promote_type(Int, Real)
    @test promote_symtype(+, BigInt, BigFloat) == BigFloat
    @test promote_symtype(+, BigFloat, BigInt) == BigFloat
    @test promote_symtype(-, BigFloat, BigFloat) == BigFloat
    @test promote_symtype(*, BigFloat, BigFloat) == BigFloat
end

@testset "promote_symtype with Rational and BigInt" begin
    # Rational and BigInt combinations
    @test promote_symtype(+, Rational{Int}, BigInt) == Real
    @test promote_symtype(+, BigInt, Rational{Int}) == Real
end

@testset "promote_symtype with Rational and Integer" begin
    # Rational and Integer combinations
    @test promote_symtype(+, Rational{Int}, Int) == Real
    @test promote_symtype(+, Int, Rational{Int}) == Real
    @test promote_symtype(+, Complex{Rational{Int}}, Int) == Complex{Real}
    @test promote_symtype(+, Int, Complex{Rational{Int}}) == Complex{Real}
end

@testset "promote_symtype with Complex{Rational} and BigInt" begin
    # Complex{Rational} and BigInt
    @test promote_symtype(+, Complex{Rational{Int}}, BigInt) == Complex{Real}
    @test promote_symtype(+, BigInt, Complex{Rational{Int}}) == Complex{Real}
end

@testset "promote_symtype for division with Integer/Rational" begin
    # division promote_symtype
    @test promote_symtype(/, Int, Int) == Real
    @test promote_symtype(/, Rational{Int}, Int) == Real
    @test promote_symtype(/, Int, Rational{Int}) == Real
    @test promote_symtype(/, Complex{Int}, Int) == Complex{promote_type(Int, Real)}
    @test promote_symtype(/, Int, Complex{Int}) == Complex{promote_type(Real, Int)}
    @test promote_symtype(/, Complex{Float64}, Complex{Int}) == Complex{promote_type(promote_type(Float64, Int), Real)}

    # Backslash operator
    @test promote_symtype(\, Int, Int) == Real
    @test promote_symtype(\, Rational{Int}, Int) == Real
    @test promote_symtype(\, Int, Rational{Int}) == Real
end

@testset "promote_symtype for identity" begin
    @test promote_symtype(identity, Float64) == Float64
    @test promote_symtype(identity, Int) == Int
end

@testset "promote_shape for identity" begin
    @test promote_shape(identity, ShapeVecT()) == ShapeVecT()
    @test promote_shape(identity, ShapeVecT((1:2, 1:3))) == ShapeVecT((1:2, 1:3))
end
@testset "promote_symtype for hvncat" begin
    @test promote_symtype(hvncat, NTuple{2, Int}, Int, Float64, Int32) == Array{Float64, 2}
    @test promote_symtype(hvncat, NTuple{3, Int}, Int, Int, Int) == Array{Int, 3}
end

@testset "promote_symtype for rem2pi" begin
    @test promote_symtype(rem2pi, Float64, typeof(RoundNearest)) == Float64
end

@testset "promote_shape for diadic functions with arrays" begin
    sh_arr = ShapeVecT((1:2,))
    @test_throws ArgumentError promote_shape(max, sh_arr, ShapeVecT())
    @test_throws ArgumentError promote_shape(max, ShapeVecT(), sh_arr)
end

@testset "promote_shape for NaNMath.pow" begin
    @test promote_shape(NaNMath.pow, ShapeVecT(), ShapeVecT()) == ShapeVecT()
end

@testset "promote_shape for log with matrices" begin
    @test promote_shape(log, Unknown(2)) == Unknown(2)
    @test promote_shape(log, Unknown(-1)) == Unknown(-1)
    @test promote_shape(log, ShapeVecT()) == ShapeVecT()
    @test promote_shape(log, ShapeVecT((1:2, 1:2))) == ShapeVecT((1:2, 1:2))
    @test_throws ArgumentError promote_shape(log, ShapeVecT((1:3,)))

    @test promote_shape(NaNMath.log, Unknown(2)) == Unknown(2)
end

@testset "promote_shape for monadic functions with arrays" begin
    @test_throws ArgumentError promote_shape(sin, ShapeVecT((1:2,)))
end

@testset "promote_shape for rem2pi" begin
    @test promote_shape(rem2pi, ShapeVecT(), ShapeVecT()) == ShapeVecT()
    @test_throws ArgumentError promote_shape(rem2pi, ShapeVecT((1:2,)), ShapeVecT())
end

@testset "promote_symtype for inv with error" begin
    @test_throws ErrorException promote_symtype(inv, String)
end

@testset "promote_shape for inv" begin
    @test promote_shape(inv, Unknown(-1)) == Unknown(-1)
    @test promote_shape(inv, Unknown(2)) == Unknown(2)
    @test promote_shape(inv, ShapeVecT()) == ShapeVecT()
    @test promote_shape(inv, ShapeVecT((1:2, 1:3))) == ShapeVecT((1:3, 1:2))
    @test_throws ArgumentError promote_shape(inv, ShapeVecT((1:2,)))
end

@testset "literal_pow promote_symtype" begin
    result = promote_symtype(Base.literal_pow, typeof(^), Float64, Type{Val{2}})
    @test result == promote_symtype(^, Float64, Int) || result == Any
end

@testset "default promote_symtype" begin
    function foofn end
    @test promote_symtype(foofn, Float64) == promote_type(Float64, Real)
end

@testset "promote_symtype for real" begin
    @test promote_symtype(real, Complex{Float64}) == Float64
    @test promote_symtype(real, Float64) == Float64
end

@testset "promote_shape for real/imag/conj" begin
    @test promote_shape(real, ShapeVecT((1:2, 1:3))) == ShapeVecT((1:2, 1:3))
    @test promote_shape(imag, ShapeVecT((1:2,))) == ShapeVecT((1:2,))
    @test promote_shape(conj, ShapeVecT()) == ShapeVecT()
end

@testset "real on symbolic" begin
    @syms z::Complex{Float64}
    r = real(z)
    @test symtype(r) == Real

    @syms x::Real
    @test real(x) === x
end

@testset "promote_symtype for imag" begin
    @test promote_symtype(imag, Complex{Float64}) == Float64
    @test promote_symtype(imag, Float64) == Float64
end

@testset "promote_symtype for adjoint" begin
    @test promote_symtype(adjoint, Float64) == Float64
    @test promote_symtype(adjoint, Matrix{Float64}) == Matrix{Float64}
end

@testset "promote_shape for adjoint" begin
    @test promote_shape(adjoint, Unknown(2)) == Unknown(2)
    @test_throws ArgumentError promote_shape(adjoint, Unknown(3))
    @test_throws ArgumentError promote_shape(adjoint, Unknown(0))
    @test promote_shape(adjoint, ShapeVecT()) == ShapeVecT()
    @test promote_shape(adjoint, ShapeVecT((1:3,))) == ShapeVecT((1:1, 1:3))
    @test promote_shape(adjoint, ShapeVecT((1:2, 1:3))) == ShapeVecT((1:3, 1:2))
    @test_throws ArgumentError promote_shape(adjoint, Unknown(0))
end

@testset "Boolean operators with type errors" begin
    @syms a::Real b::Real
    @syms p::Bool q::Bool

    # Test that operations work
    @test symtype(a == b) == Bool
    @test symtype(a != b) == Bool
    @test symtype(a < b) == Bool
    @test symtype(a <= b) == Bool
    @test symtype(a > b) == Bool
    @test symtype(a >= b) == Bool
    @test symtype(isless(a, b)) == Bool
    @test symtype(p & q) == Bool
    @test symtype(p | q) == Bool
    @test symtype(xor(p, q)) == Bool

    # Test with mixed symbolic and concrete
    @test symtype(a == 1.0) == Bool
    @test symtype(1.0 == a) == Bool
end

@testset "Boolean negation" begin
    @syms p::Bool
    @test symtype(!p) == Bool
    @test symtype(~p) == Bool

    @syms x::Real
    @test_throws MethodError !x
end

@testset "ifelse with error" begin
    @syms x::Real
    @test_throws ArgumentError promote_symtype(ifelse, Real, Int, Float64)
end

@testset "IndexStyle" begin
    @test Base.IndexStyle(BasicSymbolic) == Base.IndexCartesian()
end

@testset "CartesianIndex promote" begin
    @test promote_symtype(CartesianIndex, Int, Int) == CartesianIndex{2}
    @test promote_symtype(CartesianIndex{3}, Int, Int, Int) == CartesianIndex{3}
end

@testset "CartesianIndex promote_shape" begin
    sh1 = promote_shape(CartesianIndex, ShapeVecT(), ShapeVecT())
    @test sh1 == ShapeVecT((1:2,))

    sh2 = promote_shape(CartesianIndex{2}, ShapeVecT(), ShapeVecT())
    @test sh2 == ShapeVecT((1:2,))
end

@testset "clamp promote_symtype" begin
    @test promote_symtype(clamp, Float64, Int, Float32) == Float64
    @test promote_symtype(clamp, Vector{Float64}, Vector{Int}, Vector{Float32}) == Vector{Float64}
end

@testset "clamp promote_shape" begin
    sh = promote_shape(clamp, ShapeVecT(), ShapeVecT(), ShapeVecT())
    @test sh == ShapeVecT()
    shu = promote_shape(clamp, Unknown(1), Unknown(1), Unknown(1))
    @test shu == Unknown(1)
end

@testset "LinearAlgebra.dot promote" begin
    sh = promote_shape(LinearAlgebra.dot, ShapeVecT((1:3,)), ShapeVecT((1:3,)))
    @test sh == ShapeVecT()

    @test promote_symtype(LinearAlgebra.dot, Float64, Int) == Float64
    @test promote_symtype(LinearAlgebra.dot, Vector{Float64}, Vector{Int}) == Float64
end

@testset "LinearAlgebra.det promote" begin
    @test promote_symtype(LinearAlgebra.det, Float64) == Float64
    @test promote_symtype(LinearAlgebra.det, Matrix{Float64}) == Float64

    sh1 = promote_shape(LinearAlgebra.det, Unknown(-1))
    @test sh1 == ShapeVecT()

    sh2 = promote_shape(LinearAlgebra.det, Unknown(2))
    @test sh2 == ShapeVecT()

    sh3 = promote_shape(LinearAlgebra.det, ShapeVecT())
    @test sh3 == ShapeVecT()

    sh4 = promote_shape(LinearAlgebra.det, ShapeVecT((1:2, 1:2)))
    @test sh4 == ShapeVecT()

    @test_throws ArgumentError promote_shape(LinearAlgebra.det, Unknown(3))
    @test_throws ArgumentError promote_shape(LinearAlgebra.det, ShapeVecT((1:3,)))
end

@testset "Array symbolic operations" begin
    @syms a[1:3]::Float64 b[1:3]::Float64

    # Test size, axes, length operations
    @test size(a) == (3,)
    @test length(a) == 3
    @test ndims(a) == 1
    ax = axes(a)
    @test ax == (1:3,)
    ax1 = axes(a, 1)
    @test ax1 == 1:3

    bc = Base.broadcastable(a)
    @test bc === a

    @syms x::Float64
    bc_scalar = Base.broadcastable(x)
    @test isa(bc_scalar, Base.RefValue)

    # First iteration
    iter_result = iterate(a)
    @test iter_result !== nothing

    ei = eachindex(a)
    @test isa(ei, CartesianIndices)
end

@testset "Complex number operations with Const" begin
    @syms z::Complex{Float64}

    # Create a symbolic Const
    c1 = Const{SymReal}(1.0 + 2.0im)

    @test isequal(real(c1), Const{SymReal}(1.0))
    @test isequal(conj(c1), Const{SymReal}(1.0 - 2.0im))
    @test isequal(imag(c1), Const{SymReal}(2.0))
end

@testset "More numeric operations on symbolics" begin
    @syms x::Float64

    # Test various functions to increase coverage
    @test operation(sign(x)) === sign
    @test operation(signbit(x)) === signbit
    @test operation(ceil(x)) === ceil
    @test operation(floor(x)) === floor

    @syms n::Int
    @test operation(factorial(n)) === factorial
end

@testset "CartesianIndex with symbolics" begin
    @syms i::Int j::Int
    ci = CartesianIndex(i, j)
    @test isa(ci, BasicSymbolic)
end

@testset "Promote symtype for array operations" begin
    @test promote_symtype(+, Matrix{Float64}, Matrix{Int}) == Matrix{Float64}
    @test promote_symtype(*, Matrix{Float64}, Matrix{Int}) == Matrix{Float64}
    @test promote_symtype(*, Matrix{Float64}, Vector{Int}) == Vector{Float64}
    @test promote_symtype(*, Vector{Float64}, Int) == Vector{promote_symtype(*, Float64, Int)}
    @test promote_symtype(*, Int, Vector{Float64}) == Vector{promote_symtype(*, Int, Float64)}
    @test promote_symtype(^, Float64, Matrix{Int}) == Matrix{promote_type(Float64, Int)}
    @test promote_symtype(\, Float64, Vector{Int}) == Vector{promote_symtype(/, Int, Float64)}
    @test promote_symtype(\, Vector{Float64}, Vector{Int}) == promote_symtype(/, Int, Float64)
    @test promote_symtype(\, Matrix{Float64}, Vector{Int}) == Vector{promote_symtype(/, Int, Float64)}
    @test promote_symtype(\, Matrix{Float64}, Matrix{Int}) == Matrix{promote_symtype(/, Int, Float64)}
    @test promote_symtype(/, Matrix{Float64}, Matrix{Int}) == Matrix{promote_symtype(/, Float64, Int)}
    @test promote_symtype(/, Float64, Vector{Int}) == Matrix{promote_symtype(/, Float64, Int)}
    @test promote_symtype(/, Vector{Float64}, Float64) == Vector{promote_symtype(/, Float64, Float64)}
end

@testset "Map operations on symbolics" begin
    @syms a[1:3]::Float64 b[1:3]::Float64

    result = map(sin, a)
    @test isequal(collect(result), [sin(a[1]), sin(a[2]), sin(a[3])])

    result2 = map(+, a, b)
    @test isequal(collect(result2), [a[1] + b[1], a[2] + b[2], a[3] + b[3]])

    result3 = map(+, a, [1.0, 2.0, 3.0])
    @test isequal(collect(result3), [a[1] + 1.0, a[2] + 2.0, a[3] + 3.0])
end

@testset "in operator on symbolics" begin
    @syms x::Float64 a[1:3]::Float64

    @test promote_symtype(in, Float64, Vector{Float64}) == Bool

    psh = promote_shape(in, ShapeVecT(), ShapeVecT((1:3,)))
    @test psh == ShapeVecT()

    result = in(x, a)
    @test isa(result, BasicSymbolic)
    @test symtype(result) == Bool

    result2 = in(1.0, a)
    @test isa(result2, BasicSymbolic)

    result3 = in(x, [1.0, 2.0, 3.0])
    @test isa(result3, BasicSymbolic)
end

@testset "Symbol conversion" begin
    @syms x::Float64
    sym = Symbol(x)
    @test isa(sym, Symbol)
end
