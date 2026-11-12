using SymbolicUtils
using Test

const ANM = SymbolicUtils.AnyNumber
const AN = ANM.AnyNumber
const CONCRETE_TYPES = ANM.CONCRETE_TYPES

an_vals = Dict(
    Int => Int(3),
    Float64 => 2.5,
    Rational{Int} => 2 // 3,
    Complex{Int} => Complex{Int}(1, 2),
    ComplexF64 => 1.5 + 2.5im,
)

@testset "construction and wrapping" begin
    a = AN(3)
    @test a.is_concrete && a.concrete == 3
    @test AN(2.5).is_concrete && AN(2.5).concrete == 2.5
    @test AN(1 // 2).is_concrete
    @test AN(1 + 2im).is_concrete && AN(1 + 2im).concrete isa Complex{Int}
    @test AN(1.0 + 2im).is_concrete && AN(1.0 + 2im).concrete isa ComplexF64

    b = AN(big"2.5")
    @test !b.is_concrete && b.other == big"2.5"
    @test !AN(Float32(1)).is_concrete
    @test !AN(Complex{Rational{Int}}(1 // 2, 1 // 3)).is_concrete
    @test !AN(true).is_concrete

    @test AN(a) === a
    @test convert(AN, a) === a
    @test convert(AN, 3).concrete == 3
    @test ANM._wrap(AN(2)) === AN(2)
end

@testset "arithmetic stays concrete when the result does" begin
    for (T, v) in pairs(an_vals)
        @test AN(v).is_concrete
    end
    @test (AN(3) + AN(2)).concrete == 5
    @test (AN(3) - AN(2)).concrete == 1
    @test (AN(3) * AN(2.5)).concrete == 7.5
    @test (AN(3) / AN(2)).concrete == 1.5
    @test (AN(3) \ AN(6)).concrete == 2.0
    @test (AN(3) // AN(2)).concrete == 3 // 2
    @test (AN(3) ^ AN(2)).concrete == 9
    @test (AN(2) ^ -1).concrete == 0.5
    @test (AN(1) + AN(1 + 2im)).concrete isa Complex{Int}
    @test (AN(1.5) + AN(1 + 2im)).concrete isa ComplexF64
    @test (AN(1 + 2im) ^ 2).concrete == (1 + 2im)^2
    @test div(AN(7), AN(2)).concrete == 3
    @test fld(AN(7), AN(2)).concrete == 3
    @test mod(AN(7), AN(3)).concrete == 1
    @test rem(AN(7), AN(3)).concrete == 1
    @test gcd(AN(4), AN(6)).concrete == 2
    @test lcm(AN(4), AN(6)).concrete == 12
    @test min(AN(1), AN(2)).concrete == 1
    @test max(AN(1), AN(2)).concrete == 2
    @test hypot(AN(3), AN(4)).concrete == 5.0
    @test atan(AN(1), AN(2)).concrete == atan(1, 2)
    @test ldexp(AN(1.5), AN(2)).concrete == 6.0
    @test copysign(AN(1.5), AN(-1)).concrete == -1.5
    @test flipsign(AN(1.5), AN(-1)).concrete == -1.5
    @test (AN(1) << AN(2)).concrete == 4
    @test (AN(5) & AN(3)).concrete == 1
    @test xor(AN(5), AN(3)).concrete == 6
    @test invmod(AN(3), AN(7)).concrete == 5
end

@testset "demotion to `other`" begin
    r = AN(1 // 2) * AN(1 + 2im)              # Complex{Rational{Int}}
    @test !r.is_concrete
    @test r.other == (1 // 2) * (1 + 2im)

    @test !(AN(2) * AN(big"3")).is_concrete   # BigInt stays `other`
    @test widemul(AN(2), AN(3)) == 6          # Int128 -> other
    @test !(widemul(AN(2), AN(3))).is_concrete

    # `other`-path results re-enter the concrete path when they land back in
    # the union — `1.5 + Float32(1)` promotes to `Float64`
    r2 = AN(1.5) + AN(Float32(1))
    @test r2 == 2.5 && r2.is_concrete
    x = AN(0, false, Complex{Rational{Int}}(1 // 2, 0))
    @test real(x) == 1 // 2 && real(x).is_concrete
end

@testset "unary ops and predicates" begin
    @test (-AN(3)).concrete == -3
    @test (+AN(3)).concrete == 3
    @test abs(AN(-3)).concrete == 3
    @test abs(AN(1 + 2im)).concrete ≈ sqrt(5)
    @test abs2(AN(1 + 2im)).concrete == 5
    @test sign(AN(-2.0)).concrete == -1.0
    @test conj(AN(1 + 2im)).concrete == 1 - 2im
    @test real(AN(1 + 2im)).concrete == 1
    @test imag(AN(1 + 2im)).concrete == 2
    @test float(AN(2)).concrete == 2.0
    @test inv(AN(2)).concrete == 0.5
    @test sqrt(AN(4.0)).concrete == 2.0
    @test exp(AN(0.0)).concrete == 1.0
    @test log(AN(1.0)).concrete == 0.0
    @test sin(AN(1.0)).concrete == sin(1.0)
    @test sinpi(AN(0.5)).concrete == 1.0
    @test floor(AN(1.9)).concrete == 1.0
    @test ceil(AN(1.1)).concrete == 2.0
    @test trunc(AN(-1.9)).concrete == -1.0
    @test round(AN(1.5)).concrete == 2.0
    @test round(AN(1.5), RoundDown).concrete == 1.0
    @test round(Int, AN(1.5), RoundUp) == 2
    @test floor(Int, AN(1.9)) == 1
    @test floor(AN(1.234); digits = 1).concrete == 1.2
    @test_throws MethodError floor(AN(1.9), RoundUp) # not a Base signature
    @test zero(AN(1 + im)).concrete == 0 + 0im
    @test one(AN(2.5)).concrete == 1.0
    @test oneunit(AN(2.5)).concrete == 1.0
    @test eps(AN(1.0)).concrete == eps(1.0)
    @test isqrt(AN(9)).concrete == 3
    @test factorial(AN(5)).concrete == 120
    @test mod2pi(AN(4.0)).concrete == mod2pi(4.0)
    @test rem2pi(AN(4.0), RoundNearest).concrete == rem2pi(4.0, RoundNearest)
    @test deg2rad(AN(180.0)).concrete ≈ π
    @test sind(AN(90)) == 1.0 && atand(AN(1.0), AN(1.0)) == 45.0
    @test cispi(AN(0.5)).concrete ≈ im
    @test nextfloat(AN(1.0)).concrete == nextfloat(1.0)
    @test bswap(AN(4)).concrete == bswap(4)
    @test rationalize(AN(1.5)).concrete == 3 // 2
    @test rationalize(Int, AN(1.5)) == 3 // 2
    @test div(AN(7), AN(2), RoundDown).concrete == 3
    @test rem(AN(7.5), AN(2.0), RoundToZero) == 1.5   # via Base's mode methods
    @test binomial(AN(5), AN(2)).concrete == 10 && binomial(AN(5), 2) == 10
    @test count_ones(AN(7)) == 3 && trailing_zeros(AN(8)) == 3
    @test big(AN(2)) == big"2" && !big(AN(2)).is_concrete

    @test iszero(AN(0)) && !iszero(AN(1))
    @test isone(AN(1)) && !isone(AN(2))
    @test isinteger(AN(2.0)) && !isinteger(AN(2.5))
    @test isinteger(AN(1 + 0im))
    @test isreal(AN(1 + 0im)) && !isreal(AN(1 + 1im))
    @test isnan(AN(NaN)) && !isnan(AN(1.0))
    @test isinf(AN(Inf)) && isfinite(AN(1.0)) && !isfinite(AN(Inf))
    @test isodd(AN(3)) && iseven(AN(4)) && !isodd(AN(4))
    @test signbit(AN(-1.0)) && !signbit(AN(1.0))
    @test ispow2(AN(4)) && !ispow2(AN(3))
end

@testset "comparisons and hashing" begin
    @test AN(2) == AN(2) && AN(2) == AN(2.0) && !(AN(2) == AN(3))
    @test AN(2) == 2 && 2 == AN(2) && AN(2.0) == 2
    @test AN(1) < AN(2) && AN(1) < 2 && 1 < AN(2)
    @test AN(1) <= AN(1) && AN(2) > AN(1) && AN(2) >= AN(2)
    @test isequal(AN(2), 2) && isequal(AN(-0.0), -0.0) && !isequal(AN(0.0), AN(-0.0))
    @test isless(AN(1), AN(2)) && isless(1, AN(2))
    @test cmp(AN(1), AN(2)) == -1 && cmp(AN(2), 1) == 1 && cmp(AN(1), AN(1)) == 0
    @test isapprox(AN(1.0), 1.0) && isapprox(AN(1.0), AN(1.0 + eps()))
    @test AN(1.0) ≈ 1.0

    @test hash(AN(2)) == hash(2)
    @test hash(AN(2.0)) == hash(2.0)
    @test hash(AN(1 // 2)) == hash(1 // 2)
    d = Dict(AN(2) => :x)
    @test d[2] == :x && d[AN(2)] == :x && d[2.0] == :x
end

@testset "promotion and mixed signatures" begin
    p = promote(AN(1), 2.0)
    @test all(x -> x isa AN, p)
    @test promote_type(AN, Int) === AN
    @test promote_type(AN, BigInt) === AN

    @test AN(1) + 2 == 3 && 2 + AN(1) == 3
    @test (AN(1) + big"2") == 3 && !(AN(1) + big"2").is_concrete
    @test (AN(1) + Float32(1)) == 2 && !(AN(1) + Float32(1)).is_concrete
    @test AN(2) * true == 2 && (AN(2) * true).is_concrete   # `2 * true` -> Int, re-enters
    @test (AN(1) << 2).concrete == 4
    @test (1 | AN(2)).concrete == 3
    @test (AN(1) // 2).concrete == 1 // 2
    @test (1 // AN(2)).concrete == 1 // 2
    @test_throws MethodError AN(1.5) // 1

    n = 3
    @test AN(2)^n == 8 && 2^AN(n) == 8 && AN(2)^AN(n) == 8
    @test AN(2)^2 == 4                    # literal_pow path
    @test AN(2)^2.0 == 4.0

    @test min(AN(1), 2) == 1 && min(AN(1), 2) isa AN
    @test max(1, AN(2)) == 2 && max(1, AN(2)) isa AN
    @test div(AN(7), 2) == 3 && mod(AN(7), 3) == 1
    @test copysign(AN(1.5), -1) == -1.5
    @test isapprox(AN(1.0), 1.0) && isapprox(1.0, AN(1.0))

    @test clamp(AN(5), 0, 3) == 3 && clamp(AN(5), 0, 3) isa AN
    @test clamp(5, AN(0), AN(3)) == 3 && clamp(5, AN(0), AN(3)) isa AN
    @test clamp(AN(1), 0, 3) == 1 && clamp(AN(1), 0, 3) isa AN
    @test fma(AN(1), 2, 3) == 5 && fma(AN(1), 2, 3) isa AN
    @test muladd(AN(2), 3, 1) == 7 && muladd(AN(2), 3, 1) isa AN
    @test powermod(AN(2), 10, 7) == 2 && powermod(AN(2), 10, 7) isa AN
end

@testset "conversion, type functions, printing" begin
    @test convert(Float64, AN(2)) === 2.0
    @test convert(ComplexF64, AN(1 + 2im)) === 1.0 + 2.0im
    @test Float64(AN(2)) === 2.0
    @test Int(AN(4)) === 4
    @test_throws InexactError Int(AN(2.5))
    @test convert(BigFloat, AN(1.5)) == big"1.5"
    @test convert(AN, big"1.5").other == big"1.5"

    @test zero(AN) == 0 && one(AN) == 1 && oneunit(AN) == 1
    @test float(AN) === AN && widen(AN) === AN

    @test repr(AN(1.5)) == "1.5"
    @test string(AN(2 // 3)) == "2//3"
    @test repr(AN(0, false, big"1.5")) == "1.5"
end

@testset "errors propagate from leaves" begin
    @test_throws DomainError sqrt(AN(-1.0))
    @test_throws MethodError AN(1.5) // 1
    @test_throws MethodError isless(AN(1 + im), AN(2))
    @test_throws MethodError mod(AN(3), AN(1 + im))
end

@testset "inference" begin
    @inferred AN(1) + AN(2)
    @inferred AN(1) < AN(2)
    @inferred sin(AN(1.0))
    @inferred AN(1) * AN(1 + 2im)
    @inferred AN(0, false, big"2") + AN(1)
    @inferred convert(Float64, AN(2))
    @inferred convert(ComplexF64, AN(1 + 2im))
    @inferred Rational{Int}(AN(1.5))
    @inferred Rational{BigInt}(AN(1.5))
    @inferred floor(Int, AN(1.5))
    @inferred round(Int, AN(1.5), RoundUp)
    @inferred rationalize(Int, AN(1.5))
    @inferred hash(AN(1), UInt(0))
end

@testset "no allocations on the concrete path" begin
    v = [AN(x, true, ANM._NOVALUE) for x in randn(1000)]
    sum_split(v) = (acc = v[1]; for i in 2:length(v); acc = acc + v[i]; end; acc)
    sum_split(v)
    @test @allocated(sum_split(v)) < 4096
end
