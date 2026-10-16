using SymbolicUtils, SymbolicUtils.Code, Test
using SymbolicUtils: Const

function count_calls(ex, f)
    n = Ref(0)
    function walk(x)
        x isa Expr || return
        Meta.isexpr(x, :call) && x.args[1] === f && (n[] += 1)
        return foreach(walk, x.args)
    end
    walk(ex)
    return n[]
end

evalwith(ex, bindings) = eval(
    :(
        let $([:($k = $v) for (k, v) in bindings]...)
            $ex
        end
    )
)
returns_buffer(buf) = SymbolicUtils.Term{SymReal}(Returns{SymReal}, (buf,))
fused(rewrites...) = Dict{Any, Any}(Code.FUSE_BROADCASTS_KEY => true, rewrites...)

@testset "eager unless enabled" begin
    @syms x[1:4] y[1:4]
    ex = Code.fast_toexpr(x[2:4] .+ 2 .* y[1:3], Dict{Any, Any}())
    @test count_calls(ex, Code.fused_materialize) == 0
    @test count_calls(ex, broadcast) == 2
end

@testset "nested broadcasts fuse into one" begin
    @syms x[1:4] y[1:4] a
    expr = (x .+ y) .* a .- sin.(x)
    ex = Code.fast_toexpr(expr, fused())
    @test count_calls(ex, Code.fused_materialize) == 1
    @test count_calls(ex, broadcast) == 0
    xv, yv, av = [0.1, 0.2, 0.3, 0.4], [1.5, -2.0, 3.25, 4.0], 0.7
    @test evalwith(ex, (:x => xv, :y => yv, :a => av)) ==
        broadcast(-, broadcast(*, broadcast(+, xv, yv), av), broadcast(sin, xv))
end

# A `broadcast` behind a call that is never inlined, as a package might spell one.
@noinline wrapped_broadcast(f, As...) = broadcast(f, As...)
Code.is_elementwise_call(::typeof(wrapped_broadcast)) = true
wrap_broadcasts(x) = SymbolicUtils.Term{SymReal}(
    wrapped_broadcast, collect(Any, SymbolicUtils.arguments(x));
    type = SymbolicUtils.symtype(x), shape = SymbolicUtils.shape(x)
)

@testset "wrappers of broadcast fuse like broadcast" begin
    @syms x[1:4] y[1:4] a
    expr = wrap_broadcasts(broadcast(-, wrap_broadcasts(broadcast(*, x, a)), y))
    xv, yv, av = [0.1, 0.2, 0.3, 0.4], [1.5, -2.0, 3.25, 4.0], 0.7
    expected = broadcast(-, broadcast(*, xv, av), yv)

    eager = Code.fast_toexpr(expr, Dict{Any, Any}())
    @test count_calls(eager, wrapped_broadcast) == 2
    @test evalwith(eager, (:x => xv, :y => yv, :a => av)) == expected

    ex = Code.fast_toexpr(expr, fused())
    @test count_calls(ex, wrapped_broadcast) == 0
    @test count_calls(ex, Code.fused_materialize) == 1
    @test evalwith(ex, (:x => xv, :y => yv, :a => av)) == expected

    # Larger than `Code.FILL_ARR_LIMIT`, so the `ArrayMaker` is not scalarized whole.
    @syms u[1:10] v[1:10]
    w = @makearray w[1:20] begin
        w[1:10] => wrap_broadcasts(broadcast(+, u, v))
        w[11:20] => wrap_broadcasts(broadcast(*, a, u))
    end
    ex = Code.fast_toexpr(w, fused())
    @test count_calls(ex, wrapped_broadcast) == 0
    @test count_calls(ex, Code.fused_materialize!) == 2
    uv, vv = collect(1.0:10.0), collect(0.5:0.5:5.0)
    @test evalwith(ex, (:u => uv, :v => vv, :a => av)) == [uv .+ vv; av .* uv]
end

@testset "a node used twice is materialized once" begin
    @syms x[1:3] y[1:3]
    s = x .* y
    expr = s .+ s ./ 2
    ex = Code.fast_toexpr(expr, fused())
    @test count_calls(ex, Code.fused_materialize) == 2
    xv, yv = [1.0, 2.0, 3.0], [0.5, 0.25, 0.125]
    sv = xv .* yv
    @test evalwith(ex, (:x => xv, :y => yv)) == broadcast(+, sv, broadcast(/, sv, 2))
end

@testset "array sums and scalar products fuse" begin
    @syms x[1:3] y[1:3] a
    expr = x + (-1) * (a .* y)
    ex = Code.fast_toexpr(expr, fused(:sort_addmul => false))
    @test count_calls(ex, Code.fused_materialize) == 1
    @test count_calls(ex, +) == 0
    xv, yv, av = [1.0, 2.0, 3.0], [0.3, 0.6, 0.9], 1.1
    @test evalwith(ex, (:x => xv, :y => yv, :a => av)) == xv + (-1) * (av .* yv)
end

@testset "matrix products are not fused" begin
    @syms A[1:2, 1:2] B[1:2, 1:2]
    expr = (A * B) .+ 1
    ex = Code.fast_toexpr(expr, fused())
    Av, Bv = [1.0 2.0; 3.0 4.0], [0.5 0.0; 1.0 2.0]
    @test evalwith(ex, (:A => Av, :B => Bv)) == (Av * Bv) .+ 1
end

@testset "slices of arguments are read through views" begin
    @syms x[1:6]
    expr = x[2:5] .- 2 .* x[1:4]
    ex = Code.fast_toexpr(expr, fused())
    @test count_calls(ex, view) == 2
    @test count_calls(ex, Code.fused_materialize) == 1
    xv = [1.0, 4.0, 9.0, 16.0, 25.0, 36.0]
    @test evalwith(ex, (:x => xv,)) == xv[2:5] .- 2 .* xv[1:4]
end

@testset "slices of computed arrays stay copies" begin
    @syms x[1:6]
    expr = (x .^ 2)[2:5] .+ 1
    ex = Code.fast_toexpr(expr, fused())
    @test count_calls(ex, view) == 0
    xv = collect(1.0:6.0)
    @test evalwith(ex, (:x => xv,)) == (xv .^ 2)[2:5] .+ 1
end

# `ArrayMaker`s of at most `Code.FILL_ARR_LIMIT` elements are scalarized whole, so these
# use larger arrays.
@testset "region writes" begin
    @syms x[1:11] y[1:3, 1:4] out[1:22]
    w = @makearray w[1:22] begin
        w[1:10] => x[2:11] .- x[1:10]
        w[11:22] => vec(y .* 3 .+ x[1:3])
    end
    xv = cumsum(1.0:11.0)
    yv = reshape(collect(1.0:12.0), 3, 4)
    expected = [diff(xv); vec(yv .* 3 .+ xv[1:3])]

    @testset "fresh buffer" begin
        ex = Code.fast_toexpr(w, fused())
        @test count_calls(ex, Code.fused_materialize!) == 2
        @test count_calls(ex, copyto!) == 0
        @test evalwith(ex, (:x => xv, :y => yv)) == expected
    end

    @testset "output buffer argument" begin
        rewrites = fused(Code.ALLOCATOR_REWRITES_KEY => returns_buffer(out))
        ex = Code.fast_toexpr(w, rewrites)
        buf = zeros(22)
        @test evalwith(ex, (:x => xv, :y => yv, :out => buf)) === buf
        @test buf == expected
    end
end

@testset "views never read data the same function already overwrote" begin
    # Every region reads `x` through views while writing `out`; called with `out === x`, a
    # region must still see `x` as it was on entry, not as earlier regions left it.
    @syms x[1:20] out[1:20]
    w = @makearray w[1:20] begin
        w[1:10] => x[11:20] .+ 1
        w[11:20] => x[1:10] .* 2
    end
    rewrites = fused(Code.ALLOCATOR_REWRITES_KEY => returns_buffer(out))
    ex = Code.fast_toexpr(w, rewrites)
    @test count_calls(ex, Base.unalias) == 1
    @test count_calls(ex, Code.fused_materialize!) == 2

    xv = collect(1.0:20.0)
    expected = [xv[11:20] .+ 1; xv[1:10] .* 2]
    buf = zeros(20)
    evalwith(ex, (:x => xv, :out => buf))
    @test buf == expected

    shared = copy(xv)
    evalwith(ex, (:x => shared, :out => shared))
    @test shared == expected
end

@testset "single-element regions" begin
    @syms x[1:20] y[1:20]
    w = @makearray w[1:21] begin
        w[1:20] => x .+ y
        w[21:21] => x[20:20] .* y[1:1]
    end
    xv, yv = collect(1.0:20.0), collect(21.0:40.0)
    expected = [xv .+ yv; xv[20] * yv[1]]
    for scalarize in (true, false)
        rewrites = fused(:scalarize_single_element_regions => scalarize)
        @test evalwith(Code.fast_toexpr(w, rewrites), (:x => xv, :y => yv)) == expected
    end
end

# Stands in for a GPU array: broadcasts and block copies work, scalar indexing throws.
struct NoScalarVector{T, A <: AbstractVector{T}} <: AbstractVector{T}
    data::A
end
Base.size(x::NoScalarVector) = size(x.data)
Base.getindex(::NoScalarVector, ::Int) = error("scalar getindex on NoScalarVector")
Base.setindex!(::NoScalarVector, _, ::Int) = error("scalar setindex! on NoScalarVector")
Base.view(x::NoScalarVector, r::AbstractUnitRange) = NoScalarVector(view(x.data, r))
Base.copyto!(dst::NoScalarVector, bc::Broadcast.Broadcasted) = (copyto!(dst.data, bc); dst)

@testset "regions are written without scalar indexing" begin
    @syms x[1:20] out[1:20]
    w = @makearray w[1:20] begin
        w[1:19] => x[2:20] .- x[1:19]
        w[20:20] => 2 .* x[20:20]
    end
    rewrites = fused(
        Code.ALLOCATOR_REWRITES_KEY => returns_buffer(out),
        :scalarize_single_element_regions => false
    )
    ex = Code.fast_toexpr(w, rewrites)
    xv = collect(1.0:20.0) .^ 2
    buf = NoScalarVector(zeros(20))
    evalwith(ex, (:x => xv, :out => buf))
    @test buf.data == [diff(xv); 2 * xv[20]]
end

@testset "in-place updates read the written region through the destination" begin
    # `out` is `x`'s memory, and each region reads `x` only where it writes it.
    @syms x[1:20] y[1:20] dt out[1:20]
    w = @makearray w[1:20] begin
        w[1:10] => x[1:10] .+ dt .* y[1:10]
        w[11:20] => x[11:20] .- dt .* y[11:20]
    end
    xv, yv, dtv = collect(1.0:20.0), collect(0.5:0.5:10.0), 0.1
    expected = [xv[1:10] .+ dtv .* yv[1:10]; xv[11:20] .- dtv .* yv[11:20]]
    in_place = fused(
        Code.ALLOCATOR_REWRITES_KEY => returns_buffer(out),
        Code.FUSE_UNALIAS_KEY => false, Code.FUSE_OUTPUT_ARRAY_KEY => x
    )
    ex = Code.fast_toexpr(w, in_place)
    @test count_calls(ex, Base.unalias) == 0
    @test count_calls(ex, Code.fused_materialize_noalias!) == 2
    # One view of `out` per region and one of `y`; `x` is read through `out`'s views.
    @test count_calls(ex, view) == 4

    shared = copy(xv)
    evalwith(ex, (:x => shared, :y => yv, :dt => dtv, :out => shared))
    @test shared == expected

    # Same values as the unaliasing codegen, without its copies of `x`.
    unaliased = fused(Code.ALLOCATOR_REWRITES_KEY => returns_buffer(out))
    @eval update_unaliased!(x, y, dt, out) = $(Code.fast_toexpr(w, unaliased))
    @eval update_in_place!(x, y, dt, out) = $ex
    a, b = copy(xv), copy(xv)
    update_unaliased!(a, yv, dtv, a)
    update_in_place!(b, yv, dtv, b)
    @test a == b == expected
    update_in_place!(b, yv, dtv, b)
    @test (@allocated update_in_place!(b, yv, dtv, b)) < (@allocated update_unaliased!(a, yv, dtv, a))
end
