using SymbolicUtils, Test
using SymbolicUtils: Const, SymReal, TreeReal, BasicSymbolic, ShapeVecT, shape, term, maketerm,
    operation, arguments

@testset "Empty index ranges remain empty slices" begin
    @syms x[1:2, 1:3] y[1:2, 1:3]
    xt = SymbolicUtils.Sym{TreeReal}(:xt; type = Matrix{Real}, shape = ShapeVecT([1:2, 1:3]))
    for indices in ((1:0, Colon()), (Colon(), 1:0), (1:0, 1:0), (1:1, 2:3))
        expected = zeros(2, 3)[indices...]
        sliced = x[indices...]
        @test size(sliced) == size(expected)
        @test size(SymbolicUtils.scalarize(sliced)) == size(expected)
        @test size(sliced[:, :]) == size(expected)
        # Every construction path must agree with `getindex` on the resulting shape.
        @test size(substitute(sliced, Dict(x => y); fold = Val(false))) == size(expected)
        @test size(term(getindex, x, indices...)) == size(expected)
        @test length.(SymbolicUtils.promote_shape(getindex, shape(x), shape.(indices)...)) ==
            collect(size(expected))
        cargs = [x; [Const{SymReal}(i) for i in indices]]
        @test size(maketerm(BasicSymbolic{SymReal}, getindex, cargs, nothing)) == size(expected)
        @test size(maketerm(BasicSymbolic{TreeReal}, getindex, Any[xt, indices...], nothing)) ==
            size(expected)
    end
    colon = Const{SymReal}(Colon())
    empty_range = Const{SymReal}(1:0)
    @test size(x[colon, 1:0]) == (2, 0)
    @test size(x[empty_range, :]) == (0, 3)
end

@testset "Slicing an empty slice keeps the empty index" begin
    @syms x[1:2, 1:3] y[1:2, 1:3]
    for (outer, inner) in (
            ((1:0, :), (:, :)), ((1:0, :), (:, 1:2)), ((:, 1:0), (1:2, :)),
        )
        expected = zeros(2, 3)[outer...][inner...]
        sliced = x[outer...][inner...]
        @test size(sliced) == size(expected)
        rebuilt = maketerm(
            BasicSymbolic{SymReal}, operation(sliced), arguments(sliced), nothing
        )
        @test size(rebuilt) == size(expected)
        @test size(substitute(sliced, Dict(x => y); fold = Val(false))) == size(expected)
    end
end
