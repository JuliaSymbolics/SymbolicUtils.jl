using SymbolicUtils, Test
using SymbolicUtils: Sym, SymReal, ShapeVecT, clear_cache!

@testset "Nested array reductions retain their own scratch buffers" begin
    for (S, P) in ((1, 1), (1, 3), (2, 1), (2, 3)), n in 1:16
        x = Sym{SymReal}(Symbol(:reduction_x, S, :_, P, :_, n); type = Matrix{Real}, shape = ShapeVecT([1:S, 1:P]))
        y = Sym{SymReal}(Symbol(:reduction_y, S, :_, P, :_, n); type = Matrix{Real}, shape = ShapeVecT([1:S, 1:P]))
        expr = broadcast(+, x, broadcast(*, 0, y))
        # Exercise an uncached reduction after constructing nested broadcasts.
        clear_cache!(SymbolicUtils.reduce_eliminated_idxs_1)
        clear_cache!(SymbolicUtils._getindex_1)
        for index in CartesianIndices((S, P))
            @test isequal(expr[Tuple(index)...], x[Tuple(index)...])
        end
    end
end
