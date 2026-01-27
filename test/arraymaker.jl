using SymbolicUtils
using SymbolicUtils.Code
using TermInterface
using Test

@syms x[1:3]::Real y[1:3]::Real z[1:3]::Real
@testset "macro" begin
    w = @makearray w[1:3, 1:3] begin
        w[1:1, 1:3] => x'
        w[2:2, 1:3] => @arrayop (1, i) y[i] + z[i]
        w[3:3, 1:1] => [1;;]
        w[3:3, 2:2] => [z[1];;]
        w[3:3, 3:3] => [z'z;;]
    end

    truew = BS[
        x[1] x[2] x[3]
        y[1] + z[1] y[2] + z[2] y[3] + z[3]
        1 z[1] z'z
    ]
    @test isequal(collect(w), truew)

    @testset "round-tripping" begin
        @test isequal(w, maketerm(typeof(w), operation(w), arguments(w), nothing))
    end

    @testset "codegen" begin
        xv = rand(3)
        yv = rand(3)
        zv = rand(3)
        truev = eval(quote
            let x = $xv, y = $yv, z = $zv
                $(Code.toexpr(truew))
            end
        end)
        wv = eval(quote
            let x = $xv, y = $yv, z = $zv
                $(Code.toexpr(w))
            end
        end)
        wv_cse = eval(quote
            let x = $xv, y = $yv, z = $zv
                $(Code.toexpr(Code.cse(w)))
            end
        end)
        @test truev ≈ wv
        @test truev ≈ wv_cse
    end
end

@testset "nested" begin
    w = @makearray w[1:3, 1:3] begin
        w[1:1, 1:3] => x'
        w[2:2, 1:3] => @makearray _[1:1, 1:3] begin
            _[1:1, 1:1] => [y[1];;]
            _[1:1, 2:3] => z'[:, 1:2]
        end
        w[3:3, 1:1] => [1;;]
        w[3:3, 2:2] => [z[1];;]
        w[3:3, 3:3] => [z'z;;]
    end
    truew = BS[
        x[1] x[2] x[3]
        y[1] z'[1, 1] z'[1, 2]
        1 z[1] z'z
    ]
    @test isequal(collect(w), truew)

    @testset "indexing" begin
        @test isequal(w[1, 1], x'[1, 1])
        @test isequal(w[1, 2], x'[1, 2])
        @test isequal(w[1, 3], x'[1, 3])
        @test isequal(w[2, 1], y[1])
        @test isequal(w[2, 2], z'[1, 1])
        @test isequal(w[2, 3], z'[1, 2])
        @test isequal(w[3, 1], SymbolicUtils.Const{SymReal}(1))
        @test isequal(w[3, 2], z[1])
        @test isequal(w[3, 3], z'z)
    end
end

@testset "later ranges take priority" begin
    w = @makearray w[1:3] begin
        w[1:3] => x
        w[2:3] => y[1:2]
    end
    truew = BS[x[1], y[1], y[2]]
    @test isequal(collect(w), truew)
end

