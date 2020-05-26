using SymbolicUtils, Test
using SymbolicUtils: metadata, symtype, ArrayShape
using Base: Slice

@testset "arrays" begin
    @syms X[1:5, 2:6] (Y::Real)[1:5, 1:5] Z::Matrix{Float64}
    @test symtype(X) == AbstractArray{Number, 2}
    @test symtype(Y) == AbstractArray{Real, 2}
    @test metadata(X) == ArrayShape(Slice.((1:5, 2:6)))
    @test metadata(Y) == ArrayShape(Slice.((1:5, 1:5)))

    A = Y[2, :]
    @test symtype(A) == AbstractArray{Real, 1}
    @test axes(metadata(A)) == (1:5,)

    B = A[3:5]
    @test axes(metadata(B)) == (Slice(1:3),)

    @test metadata(Z[1:2, 3:4]) == nothing
end
