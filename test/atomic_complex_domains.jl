using Test
using SymbolicUtils

@testset "raw atomic complex domain semantics" begin
    @syms x::Real y::Real z::Complex{Real} n::Number m::Number

    @test conj(x) === x
    @test real(x) === x
    @test SymbolicUtils._iszero(imag(x))

    cz = conj(z)
    @test !isequal(cz, z)
    @test operation(cz) === conj
    @test SymbolicUtils.symtype(cz) == SymbolicUtils.symtype(z)
    @test SymbolicUtils.symtype(real(z)) <: Real
    @test SymbolicUtils.symtype(imag(z)) <: Real

    cn = conj(n)
    @test !isequal(cn, n)
    @test operation(cn) === conj
    @test SymbolicUtils.symtype(cn) == Number

    @test operation(exp(z)) === exp
    @test operation(sin(z)) === sin
    @test operation(cos(z)) === cos
    @test operation(log(z)) === log
    @test operation(sqrt(z)) === sqrt

    phase = exp(im * x)
    @test operation(phase) === exp
    @test Set(SymbolicUtils.search_variables(phase)) == Set([x])

    # Establish what the scalar eltype test in `conj` actually means. Numeric scalar
    # types are their own `eltype`; `Complex{Real}` is not misclassified as Real.
    @test eltype(Complex{Real}) == Complex{Real}

    @testset "real-valued projections are stable under rebuild" begin
        rn = real(n)
        in_ = imag(n)
        @test SymbolicUtils.symtype(rn) <: Real
        @test SymbolicUtils.symtype(in_) <: Real

        # Substitution rebuilds the Term through TermInterface/maketerm. Its inferred
        # symtype must agree with the direct constructor rather than widening back to Number.
        rn2 = substitute(rn, Dict(n => m))
        in2 = substitute(in_, Dict(n => m))
        @test SymbolicUtils.symtype(rn2) <: Real
        @test SymbolicUtils.symtype(in2) <: Real
        @test operation(rn2) === real
        @test operation(in2) === imag
    end

    @testset "magnitudes are real-valued" begin
        for v in (z, n)
            @test SymbolicUtils.symtype(abs(v)) <: Real
            @test SymbolicUtils.symtype(abs2(v)) <: Real
        end
    end

    @testset "explicit Cartesian complex terms" begin
        @test SymbolicUtils.promote_shape(complex, SymbolicUtils.ShapeVecT(), SymbolicUtils.ShapeVecT()) == SymbolicUtils.ShapeVecT()
        @test_throws ArgumentError SymbolicUtils.promote_shape(complex, SymbolicUtils.ShapeVecT((1:2,)), SymbolicUtils.ShapeVecT())

        c = SymbolicUtils.term(complex, x, y; type = Complex{Real})
        @test SymbolicUtils.symtype(c) == Complex{Real}
        @test SymbolicUtils.shape(c) == SymbolicUtils.ShapeVecT()
        @test isequal(simplify(c), c)

        # Symbolically the explicit Cartesian node stays intact, while polynomial
        # expansion interprets the same node as `re + im*im_part`.
        diff = simplify(c - (x + im * y); expand = true)
        @test SymbolicUtils._iszero(diff)

        c0 = SymbolicUtils.term(complex, 0, x; type = Complex{Real})
        @test SymbolicUtils._iszero(simplify(c0 - im * x; expand = true))
    end

    @testset "complex projection simplification (#832)" begin
        @syms r1::Real r2::Real i1::Real i2::Real z1::Complex{Real} z2::Complex{Real}
        x1 = r1 + i1 * im
        x2 = r2 + i2 * im

        # Downstream algorithms such as Symbolics' ODE solver call `real`/`imag`
        # directly and do not necessarily run a later `simplify` pass. Cartesian
        # sums/products therefore have to expose their components at construction.
        direct_im = imag((1 - im) * r1 + (1 + im) * r2)
        direct_re = real((1//5 - (3//5) * im) * r1 + ((3//5) + (1//5) * im) * r2)
        @test !(iscall(direct_im) && operation(direct_im) === imag)
        @test !(iscall(direct_re) && operation(direct_re) === real)
        @test SymbolicUtils._iszero(simplify(direct_im - (-r1 + r2); expand = true))
        @test SymbolicUtils._iszero(simplify(direct_re - ((1//5) * r1 + (3//5) * r2); expand = true))

        @test SymbolicUtils._iszero(simplify(real(x1 * x2) - (r1 * r2 - i1 * i2); expand = true))
        @test SymbolicUtils._iszero(simplify(imag(x1 * x2) - (r1 * i2 + i1 * r2); expand = true))

        reprod = simplify(real(z1 * z2))
        improd = simplify(imag(z1 * z2))
        @test SymbolicUtils._iszero(simplify(reprod - (real(z1) * real(z2) - imag(z1) * imag(z2)); expand = true))
        @test SymbolicUtils._iszero(simplify(improd - (real(z1) * imag(z2) + imag(z1) * real(z2)); expand = true))

        opaque = simplify(real(exp(z1)))
        @test iscall(opaque)
        @test operation(opaque) === real
    end
end
