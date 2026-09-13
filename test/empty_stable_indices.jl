using SymbolicUtils, Test

@testset "Stable indices respect empty axes" begin
    for shape in (
            (), (1:0,), (1:0, 1:3), (1:2, 1:0), (1:2, 1:0, 1:3),
            (1:2, 1:3), (2:3, -1:1),
        )
        indices = SymbolicUtils.StableIndices(SymbolicUtils.ShapeVecT(collect(shape)))
        expected = CartesianIndices(shape)
        @test length(indices) == length(expected)
        @test isnothing(iterate(indices)) == isempty(expected)
        visited = [Tuple(index) for index in indices]
        @test visited == vec([Tuple(index) for index in expected])
    end
end
