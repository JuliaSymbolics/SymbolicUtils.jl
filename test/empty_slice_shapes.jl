using SymbolicUtils, Test

@testset "Empty index ranges remain empty slices" begin
    @syms x[1:2, 1:3]
    for indices in ((1:0, Colon()), (Colon(), 1:0), (1:0, 1:0), (1:1, 2:3))
        expected = zeros(2, 3)[indices...]
        sliced = x[indices...]
        @test size(sliced) == size(expected)
        @test size(SymbolicUtils.scalarize(sliced)) == size(expected)
        @test size(sliced[:, :]) == size(expected)
    end
    colon = SymbolicUtils.Const{SymbolicUtils.SymReal}(Colon())
    empty_range = SymbolicUtils.Const{SymbolicUtils.SymReal}(1:0)
    @test size(x[colon, 1:0]) == (2, 0)
    @test size(x[empty_range, :]) == (0, 3)
end
