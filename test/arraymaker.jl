using SymbolicUtils
using SymbolicUtils.Code
using TermInterface
using StaticArrays
using Test
import SymbolicUtils as SU

@syms x[1:3]::Real y[1:3]::Real z[1:3]::Real

@testset "public constructor" begin
    if isdefined(Base, :ispublic)
        @test Base.ispublic(SymbolicUtils, :ArrayMaker)
    end
    maker = SymbolicUtils.ArrayMaker{SymReal}(
        [[1:3], [2:3]], [x, y[1:2]]; shape = SU.ShapeVecT((1:3,))
    )
    @test isequal(collect(maker), BS[x[1], y[1], y[2]])
end

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

@testset "`SVector` in arguments" begin
    @syms x y z
    regions = SU.RegionsT((SU.ShapeVecT((1:1,)), SU.ShapeVecT((2:2,)), SU.ShapeVecT((3:3,))))
    vals = SymbolicUtils.term(SVector{3}, [x], [y], [z])
    maker = maketerm(typeof(x), SymbolicUtils.ArrayMaker{SymReal}, SymbolicUtils.ArgsT{SymReal}((regions, vals)), nothing)
    reference = @makearray w[1:3] begin
        w[1:1] => vals[1]
        w[2:2] => vals[2]
        w[3:3] => vals[3]
    end
    @test isequal(maker, reference)
end

# Stands in for a GPU array: whole-array operations work, scalar indexing throws.
struct NoScalarVector{T, A <: AbstractVector{T}} <: AbstractVector{T}
    data::A
end
Base.size(x::NoScalarVector) = size(x.data)
Base.getindex(::NoScalarVector, ::Int) = error("scalar getindex on NoScalarVector")
Base.setindex!(::NoScalarVector, _, ::Int) = error("scalar setindex! on NoScalarVector")
Base.view(x::NoScalarVector, r::AbstractUnitRange) = NoScalarVector(view(x.data, r))
Base.copyto!(dst::NoScalarVector, src::AbstractArray) = (copyto!(dst.data, src); dst)

@testset "`:scalarize_single_element_regions` rewrite" begin
    # Longer than `Code.FILL_ARR_LIMIT`, so the output is not scalarized as a whole.
    @syms out[1:20]::Real p[1:20]::Real q[1:20]::Real a::Real
    # The in-place form `Symbolics.build_function` generates.
    iip_allocator = SU.Term{SymReal}(
        Returns, SU.ArgsT{SymReal}((out,));
        type = SU.FnType{Tuple, Any, Returns{Any}}, shape = SU.ShapeVecT()
    )
    function build_iip(regions, values, rewrites)
        maker = SU.ArrayMaker{SymReal}([[r] for r in regions], values)
        fn = Func([out, p, q, a], [], Code.with_allocator(iip_allocator, maker))
        return Code.fast_toexpr(fn, IRStructure{SymReal}(), rewrites)
    end
    as_blocks = Dict{Any, Any}(:scalarize_single_element_regions => false)
    pv, qv, av = collect(1.0:20), collect(10.0:10:200), 5.0

    # Single-element regions holding an array expression.
    cases = [
        "non-constant" => (
            [1:19, 20:20], [p[1:19] .+ q[1:19], p[20:20] .- q[1:1]],
            [pv[1:19] .+ qv[1:19]; pv[20] - qv[1]],
        ),
        "constant right-hand side" => (
            [1:1, 2:20], [SU.Const{SymReal}([2.0]) .- p[1:1], 2 .* p[2:20]],
            [2.0 - pv[1]; 2 .* pv[2:20]],
        ),
        "mixed regions" => (
            [1:1, 2:10, 11:11, 12:20],
            [p[1:1] .- q[2:2], p[2:10] .+ q[2:10], 3 .* p[11:11], q[12:20] .- p[12:20]],
            [pv[1] - qv[2]; pv[2:10] .+ qv[2:10]; 3pv[11]; qv[12:20] .- pv[12:20]],
        ),
    ]
    @testset "scalarized by default: $name" for (name, (regions, values, expected)) in cases
        ex = build_iip(regions, values, Dict{Any, Any}())
        @test occursin("batched_setindex!", string(ex))
        f = eval(ex)
        @test Base.invokelatest(f, zeros(20), pv, qv, av) ≈ expected
        @test_throws ErrorException Base.invokelatest(f, NoScalarVector(zeros(20)), pv, qv, av)
    end
    @testset "written as blocks when disabled: $name" for (name, (regions, values, expected)) in cases
        ex = build_iip(regions, values, as_blocks)
        @test !occursin("batched_setindex!", string(ex))
        f = eval(ex)
        @test Base.invokelatest(f, zeros(20), pv, qv, av) ≈ expected
        @test Base.invokelatest(f, NoScalarVector(zeros(20)), pv, qv, av).data ≈ expected
    end

    # Scalar values, such as a scalar equation's residual, are always written as scalars.
    @testset "scalar values stay scalar" for rewrites in (Dict{Any, Any}(), as_blocks)
        ex = build_iip([1:18, 19:19, 20:20], [p[1:18], SU.Const{SymReal}([a]), SU.Const{SymReal}([2.0])], rewrites)
        @test occursin("batched_setindex!", string(ex))
        @test Base.invokelatest(eval(ex), zeros(20), pv, qv, av) ≈ [pv[1:18]; av; 2.0]
    end
end

@testset "index vector regions" begin
    @syms u[1:20]::Real v[1:20]::Real Z[1:4, 1:5]::Real W[1:2, 1:2]::Real
    idxs = [2, 3, 19]
    w = @makearray w[1:20] begin
        w[1:20] => u
        w[idxs] => x
    end
    idxs[1] = 4
    @test SU.unwrap_const(arguments(w)[1]) == SU.RegionsT([SU.ShapeVecT((1:20,)), SU.ShapeVecT((2:3,)), SU.ShapeVecT((19:19,))])
    @test isequal(collect(w), [i == 2 ? x[1] : i == 3 ? x[2] : i == 19 ? x[3] : u[i] for i in 1:20])
    @test isequal(w, @makearray w[1:20] begin
        w[1:20] => u
        w[2:3] => x[1:2]
        w[19:19] => x[3:3]
    end)
    @test isequal(SU.ArrayMaker{SymReal}(((1:20,), ([2, 3, 19],)), (u, x)), w)

    uv, vv = collect(1.0:20), collect(10.0:10:200)
    values = [SU.@arrayop((i,), sin(u[i]), i in 1:10), SU.@arrayop((i,), v[i] + u[i + 10], i in 1:10)]
    maker = SU.ArrayMaker{SymReal}([[1:2:19], [20:-2:2]], values)
    expected = zeros(20)
    expected[1:2:19] = sin.(uv[1:10])
    expected[20:-2:2] = vv[1:10] .+ uv[11:20]
    fn = Func([u, v], [], maker)
    @test Base.invokelatest(eval(Code.fast_toexpr(fn, IRStructure{SymReal}(), Dict{Any, Any}())), uv, vv) ≈ expected

    filled = SU.Fill(SU.ShapeVecT((1:3,)))(SU.Const{SymReal}(7))
    f = SU.ArrayMaker{SymReal}(((1:20,), ([5, 6, 12],)), (u, filled))
    @test SU.unwrap_const(arguments(f)[1]) == SU.RegionsT([SU.ShapeVecT((1:20,)), SU.ShapeVecT((5:6,)), SU.ShapeVecT((12:12,))])
    @test isequal(SU.unwrap_const(arguments(f)[2])[2], SU.Fill(SU.ShapeVecT((1:2,)))(SU.Const{SymReal}(7)))
    ff = eval(Code.fast_toexpr(Func([u], [], f), IRStructure{SymReal}(), Dict{Any, Any}()))
    expected = copy(uv)
    expected[[5, 6, 12]] .= 7
    @test Base.invokelatest(ff, uv) == expected

    m = @makearray m[1:4, 1:5] begin
        m[1:4, 1:5] => Z
        m[[1, 3], 2:3] => W
    end
    @test isequal(m[3, 3], W[2, 2])
    @test isequal(m[2, 3], Z[2, 3])
    Zv, Wv = reshape(collect(1.0:20), 4, 5), [100.0 200.0; 300.0 400.0]
    expected = copy(Zv)
    expected[[1, 3], 2:3] = Wv
    fn = Func([Z, W], [], m)
    @test Base.invokelatest(eval(Code.fast_toexpr(fn, IRStructure{SymReal}(), Dict{Any, Any}())), Zv, Wv) == expected

    @test_throws ArgumentError SU.ArrayMaker{SymReal}(((1:3,), ([1, 3],)), ([0, 0, 0], [10, 20, 30]))
    @test_throws ArgumentError SU.ArrayMaker{SymReal}(((1:20,), ([5, 6, 12],)), (u, SU.Fill(SU.ShapeVecT((1:2,)))(SU.Const{SymReal}(7))))
    @test SU.unwrap_const.(collect(SU.ArrayMaker{SymReal}(((1:3,), ([true, false, true],)), ([0, 0, 0], [10, 30])))) == [10, 0, 30]
    @test SU.unwrap_const.(collect(SU.ArrayMaker{SymReal}(((1:3,), (trues(3),)), ([0, 0, 0], [10, 20, 30])))) == [10, 20, 30]
    @test isempty(collect(SU.ArrayMaker{SymReal}(((Int[],),), (Int[],); shape = SU.ShapeVecT((1:0,)))))
end
