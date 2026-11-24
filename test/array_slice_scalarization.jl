using SymbolicUtils, Test
using SymbolicUtils: scalarize

@testset "Scalarizing slices expands their parent array operations" begin
    for (S, P) in ((1, 1), (1, 3), (2, 1), (2, 3))
        @syms x[1:S, 1:1] y[1:S, 1:P]
        replicated = x * ones(1, P)
        residual = replicated[:, 1:1] - y[:, 1:1]
        result = scalarize(residual)
        @test isequal(result, [x[s, 1] - y[s, 1] for s in 1:S, _ in 1:1])
        @test isequal(scalarize(result), result)
        @test isequal(
            scalarize(replicated[:, 1:1], Val(true)),
            [replicated[s, 1] for s in 1:S, _ in 1:1]
        )
        product = replicated[:, 1:1] .* replicated[:, P:P]
        @test isequal(scalarize(product), [x[s, 1]^2 for s in 1:S, _ in 1:1])
    end
end
