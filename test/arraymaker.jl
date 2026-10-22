using SymbolicUtils
using SymbolicUtils.Code
using TermInterface
using StaticArrays
using Test
import SymbolicUtils as SU

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

    @syms u[1:20]::Real s[1:3]::Real
    over = @makearray o[1:20] begin
        o[1:20] => u
        o[4:6] => @arrayop (i,) sin(s[i]) i in 1:3
    end
    uv, sv = collect(1.0:20), [7.0, 8.0, 9.0]
    expected = copy(uv)
    expected[4:6] = sin.(sv)
    fn = Func([u, s], [], over)
    @test Base.invokelatest(eval(Code.fast_toexpr(fn, IRStructure{SymReal}(), Dict{Any, Any}())), uv, sv) ≈ expected
    @test Base.invokelatest(eval(Code.toexpr(fn)), uv, sv) ≈ expected

    exact = @makearray e[1:20] begin
        e[1:1] => [0]
        e[1:20] => @arrayop (i,) u[i]
    end
    fn = Func([u], [], Code.with_allocator(Returns(zeros(Int, 20)), exact))
    @test Base.invokelatest(eval(Code.fast_toexpr(fn, IRStructure{SymReal}(), Dict{Any, Any}())), fill(2^53 + 1, 20)) == fill(2^53 + 1, 20)

    sines = SU.ArrayMaker{SymReal}(((1:20,), (1:20,)), (SU.Const{SymReal}(zeros(20)), @arrayop (i,) sin(u[i])))
    fn = Func([u], [], Code.with_allocator(Returns(Any[zeros(20)...]), sines))
    @test Base.invokelatest(eval(Code.fast_toexpr(fn, IRStructure{SymReal}(), Dict{Any, Any}())), ones(20)) ≈ fill(sin(1.0), 20)
end

@testset "`Code.toexpr` writes every region value" begin
    @syms p[1:2]::Real q[1:2]::Real
    w = @makearray w[1:2] begin
        w[1:2] => p .+ q
    end
    @test Base.invokelatest(eval(Code.toexpr(Func([p, q], [], w))), [1.0, 2.0], [10.0, 20.0]) == [11.0, 22.0]

    @syms r[1:20]::Real
    a = @arrayop (i,) sin(r[i])
    b = @arrayop (i,) cos(r[i])
    f = eval(Code.toexpr(Func([a, r], [], Code.MakeTuple((SU.ArrayMaker{SymReal}(((1:20,),), (a,)), b)))))
    out = Base.invokelatest(f, fill(0.5, 20), ones(20))
    @test out[1] == fill(0.5, 20)
    @test out[2] ≈ fill(cos(1.0), 20)
end

@testset "region values computed earlier are still written" begin
    @syms p[1:20]::Real q[1:20]::Real
    a = @arrayop (i,) sin(p[i])
    w = SU.ArrayMaker{SymReal}(((1:20,), (21:40,)), (a .+ q, a))
    f = eval(Code.fast_toexpr(Func([p, q], [], w), IRStructure{SymReal}(), Dict{Any, Any}()))
    @test Base.invokelatest(f, ones(20), fill(2.0, 20)) ≈ [fill(sin(1.0) + 2, 20); fill(sin(1.0), 20)]
    g = eval(Code.fast_toexpr(Func([a], [], SU.ArrayMaker{SymReal}(((1:20,),), (a,))), IRStructure{SymReal}(), Dict{Any, Any}()))
    @test Base.invokelatest(g, fill(3.0, 20)) == fill(3.0, 20)
    wrapped = Code.with_allocator(zeros, a)
    g = eval(Code.fast_toexpr(Func([wrapped, p], [], SU.ArrayMaker{SymReal}(((1:20,),), (wrapped,))), IRStructure{SymReal}(), Dict{Any, Any}()))
    @test Base.invokelatest(g, fill(3.0, 20), ones(20)) == fill(3.0, 20)
    zero_fill = SU.Fill(SU.ShapeVecT((1:20,)))(SU.Const{SymReal}(0))
    w = SU.ArrayMaker{SymReal}(((1:20,), (1:20,)), (zero_fill, a))
    for ex in (Code.fast_toexpr(Func([zero_fill, p], [], w), IRStructure{SymReal}(), Dict{Any, Any}()), Code.toexpr(Func([zero_fill, p], [], w)))
        @test Base.invokelatest(eval(ex), fill(3.0, 20), ones(20)) ≈ fill(sin(1.0), 20)
    end
end

@testset "a nested zero fill clears the parent's buffer" begin
    @syms p[1:20]::Real buf[1:20]::Real
    a = @arrayop (i,) sin(p[i])
    zero_fill = SU.Fill(SU.ShapeVecT((1:20,)))(SU.Const{SymReal}(0))
    inner = SU.ArrayMaker{SymReal}(((1:20,), (1:20,)), (zero_fill, a))
    iip = SU.Term{SymReal}(
        Returns, SU.ArgsT{SymReal}((buf,));
        type = SU.FnType{Tuple, Any, Returns{Any}}, shape = SU.ShapeVecT()
    )
    fn = Func([p, buf], [], Code.with_allocator(iip, SU.ArrayMaker{SymReal}(((1:20,),), (inner,))))
    f = eval(Code.fast_toexpr(fn, IRStructure{SymReal}(), Dict{Any, Any}()))
    @test Base.invokelatest(f, ones(20), fill(5.0, 20)) ≈ fill(sin(1.0), 20)
end

@testset "equal empty axes hash equally" begin
    sh = SU.ShapeVecT((1:3, 1:0))
    mk(ax) = SU.ArrayMaker{SymReal}(((1:3, ax),), (SU.Const{SymReal}(zeros(3, 0)),); shape = sh)
    @test isequal(mk(1:0), mk(3:2))
    @test hash(mk(1:0)) == hash(mk(3:2))
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
