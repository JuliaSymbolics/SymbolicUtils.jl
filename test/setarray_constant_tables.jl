using SymbolicUtils
using SymbolicUtils.Code
using SymbolicUtils.Code: IRStructure
using Test
using LinearAlgebra
using SparseArrays
import SymbolicUtils as SU

# `SetArray` writes its constant elements from tables instead of one statement each.
@syms p[1:8]::Real out[1:60]::Real

build(elems; inbounds = false, rewrites = Dict{Any, Any}()) =
    Code.fast_toexpr(Func([out, p], [], SetArray(inbounds, out, elems, true)), IRStructure{SymReal}(), rewrites)
without_tables() = Dict{Any, Any}(Code.SETARRAY_CONSTANT_TABLES_KEY => false)
call(ex, args...) = Base.invokelatest(eval(ex), args...)
uses_tables(ex) = occursin(r"fill_constant_span!|fill_constant_runs!|fill_constant_at!|set_constants!", string(ex))
# The number of `a[i] = v` statements in `ex`.
function indexed_assignments(ex)
    ex isa Expr || return 0
    n = sum(indexed_assignments, ex.args; init = 0)
    return n + (ex.head === :(=) && Meta.isexpr(ex.args[1], :ref))
end

pv = collect(1.0:8.0)

@testset "dense fill" begin
    # Mostly zeros, a constant repeating in consecutive and in scattered positions,
    # one-off constants of two types, and non-constant elements.
    elems = Any[0 for _ in 1:60]
    for i in 5:14
        elems[i] = 2.5
    end
    for i in 20:3:47
        elems[i] = -1.5
    end
    elems[2] = 7
    elems[3] = 0.25
    elems[50] = -0.0
    elems[1] = p[1] * p[2]
    elems[30] = p[3] + p[4]
    elems[60] = p[8]
    expected = Float64[
        i == 1 ? pv[1] * pv[2] : i == 30 ? pv[3] + pv[4] : i == 60 ? pv[8] : elems[i] for i in 1:60
    ]

    ex = build(elems)
    str = string(ex)
    @test occursin("fill_constant_span!", str)
    @test occursin("fill_constant_runs!", str)
    @test occursin("fill_constant_at!", str)
    @test occursin("set_constants!", str)
    # Only the three non-constant elements are left as statements.
    @test indexed_assignments(ex) == 3
    @test indexed_assignments(build(elems; rewrites = without_tables())) == 60
    res = call(ex, fill(NaN, 60), pv)
    @test res == expected
    # `-0.0` is not the `0` the rest of the array is filled with.
    @test signbit(res[50])
    @test !signbit(res[49])

    ref = build(elems; rewrites = without_tables())
    @test !uses_tables(ref)
    @test call(ref, fill(NaN, 60), pv) == expected

    # The output's element type is converted to, as an assignment does.
    @test call(ex, fill(NaN32, 60), pv) == Float32.(expected)
    @test call(ex, fill(big(NaN), 60), pv) == expected
    any_res = call(ex, Vector{Any}(undef, 60), pv)
    any_ref = call(ref, Vector{Any}(undef, 60), pv)
    # No conversion: each element keeps its own type.
    @test all(i -> any_res[i] === any_ref[i], 1:60)
    @test any_res[2] === 7 && any_res[4] === 0 && any_res[3] === 0.25
    # A value is converted once per element, so mutable numbers are not shared.
    big_res = call(ex, Vector{BigFloat}(undef, 60), pv)
    @test big_res == expected
    @test big_res[5] == big_res[6] && big_res[5] !== big_res[6]
    @test big_res[15] == big_res[16] && big_res[15] !== big_res[16]
end

@testset "generated code does not grow with the number of constants" begin
    nexprs(ex) = ex isa Expr ? 1 + sum(nexprs, ex.args; init = 0) : 0
    size_with(n, rewrites) = nexprs(build(Any[i == 1 ? p[1] : 0 for i in 1:n]; rewrites))
    @test size_with(1024, Dict{Any, Any}()) == size_with(32, Dict{Any, Any}())
    @test size_with(1024, without_tables()) > 10 * size_with(1024, Dict{Any, Any}())
end

@testset "constants keep their identity" begin
    # Equal is not identical: `NaN` payloads and the precision of a `BigFloat`.
    nans = Any[reinterpret(Float64, 0x7ff8000000000000 | UInt64(i)) for i in 1:20]
    res = call(build(nans), zeros(60), pv)
    @test reinterpret.(UInt64, res[1:20]) == [0x7ff8000000000000 | UInt64(i) for i in 1:20]
    bigs = Any[BigFloat(1; precision = 64 + i) for i in 1:20]
    ex = build(bigs)
    @test uses_tables(ex)
    res = call(ex, Vector{Any}(undef, 60), pv)
    @test [precision(res[i]) for i in 1:20] == 65:84
    @test all(i -> res[i] === bigs[i], 1:20)
end

# Records every `setindex!` and stores the value without converting it.
struct LoggingVector <: AbstractVector{Int}
    log::Vector{Tuple{Int, Any}}
end
Base.size(::LoggingVector) = (40,)
Base.getindex(::LoggingVector, i::Int) = 0
Base.setindex!(v::LoggingVector, x, i::Int) = (push!(v.log, (i, x)); x)

@testset "outputs other than `Array`" begin
    # One write per element, with the value as it is, for an array with its own `setindex!`.
    elems = Any[i == 1 ? 1.5 : 0 for i in 1:40]
    ex = build(elems)
    @test uses_tables(ex)
    lv = LoggingVector(Tuple{Int, Any}[])
    call(ex, lv, pv)
    @test sort(lv.log; by = first) == [(i, i == 1 ? 1.5 : 0) for i in 1:40]
    @test all(x -> x[2] === (x[1] == 1 ? 1.5 : 0), lv.log)

    # A structured matrix rejects a zero on its diagonal, even if a one follows.
    id = Any[x for x in vec(Matrix{Int}(I, 5, 5))]
    ex = build(id)
    @test uses_tables(ex)
    @test call(ex, UnitUpperTriangular(zeros(Int, 5, 5)), pv) == I

    # A sparse vector stores what it is assigned, so no element is written twice.
    sp = Any[i == 1 ? 0 : 1 for i in 1:40]
    @test nnz(call(build(sp), spzeros(Int, 40), pv)) == nnz(call(build(sp; rewrites = without_tables()), spzeros(Int, 40), pv))

    # Not an array at all.
    d = call(build(Any[2 for _ in 1:20]), Dict{Int, Int}(), pv)
    @test d == Dict(i => 2 for i in 1:20)

    # Linear indices of a matrix.
    M = call(build(Any[i % 7 == 0 ? p[1] : i % 3 for i in 1:60]), fill(NaN, 6, 10), pv)
    @test vec(M) == [i % 7 == 0 ? pv[1] : i % 3 for i in 1:60]
end

@testset "indices that do not form one range" begin
    elems = Any[AtIndex(2i, isodd(i) ? 3.5 : p[mod1(i, 8)]) for i in 1:40]
    expected = zeros(80)
    for i in 1:40
        expected[2i] = isodd(i) ? 3.5 : pv[mod1(i, 8)]
    end
    ex = build(elems)
    @test uses_tables(ex)
    # Nothing outside the listed indices is written.
    @test call(ex, zeros(80), pv) == expected
    @test call(build(elems; rewrites = without_tables()), zeros(80), pv) == expected
end

@testset "not applied" begin
    # Fewer constants than `SETARRAY_CONSTANT_TABLES_MIN`.
    few = Any[i <= Code.SETARRAY_CONSTANT_TABLES_MIN - 1 ? 1.0 : p[1] for i in 1:20]
    @test !uses_tables(build(few))
    # A repeated index: the later write wins, so the writes cannot be reordered.
    dup = Any[AtIndex(i, 1.0) for i in 1:20]
    push!(dup, AtIndex(3, p[2]))
    push!(dup, AtIndex(3, 9.0))
    ex = build(dup)
    @test !uses_tables(ex)
    @test call(ex, zeros(60), pv)[1:20] == [i == 3 ? 9.0 : 1.0 for i in 1:20]
    # A symbolic index.
    @syms k::Int
    sym = Any[AtIndex(i, 1.0) for i in 1:20]
    push!(sym, AtIndex(k, 2.0))
    @test !uses_tables(Code.fast_toexpr(Func([out, p, k], [], SetArray(false, out, sym, true)), IRStructure{SymReal}(), Dict{Any, Any}()))
    # A hook on the left-hand sides has to see every write.
    hook = Dict{Any, Any}(Code.LHS_HOOK_KEY => (cs, i, lhs) -> lhs)
    hooked = build(Any[1.0 for _ in 1:20]; rewrites = hook)
    @test !uses_tables(hooked)
    @test indexed_assignments(hooked) == 20
end

# Numbers that code generation unwraps.
struct InnerWrapper <: Number
    value::Int
end
struct OuterWrapper <: Number
    value::InnerWrapper
end
SymbolicUtils.unwrap(w::Union{InnerWrapper, OuterWrapper}) = w.value

@testset "wrapped constants" begin
    elems = Any[OuterWrapper(InnerWrapper(3)) for _ in 1:20]
    ex = build(elems)
    @test uses_tables(ex)
    res = call(ex, Vector{Any}(undef, 60), pv)
    ref = call(build(elems; rewrites = without_tables()), Vector{Any}(undef, 60), pv)
    @test all(i -> res[i] === ref[i] === 3, 1:20)
end

@testset "elements given as an iterator" begin
    # An iterator that can only be consumed once is generated element by element.
    ex = build(Iterators.Stateful(Any[i == 2 ? p[1] : 3.0 for i in 1:20]))
    @test !uses_tables(ex)
    @test call(ex, zeros(60), pv)[1:20] == [i == 2 ? pv[1] : 3.0 for i in 1:20]
    # Any other array is read once per element.
    reads = Ref(0)
    counted = Base.Generator(i -> (reads[] += 1; i == 2 ? p[1] : 3.0), 1:20)
    ex = build(view(collect(Any, counted), :))
    @test uses_tables(ex) && reads[] == 20
    @test call(ex, zeros(60), pv)[1:20] == [i == 2 ? pv[1] : 3.0 for i in 1:20]
    @test uses_tables(build(Tuple(Any[i == 2 ? p[1] : 3.0 for i in 1:20])))
end

@testset "bounds" begin
    elems = Any[i == 1 ? p[1] : 0.5 * (i % 3) for i in 1:40]
    ex = build(elems)
    @test uses_tables(ex)
    @test_throws BoundsError call(ex, zeros(39), pv)
    @test length(call(ex, zeros(40), pv)) == 40
    inb = build(elems; inbounds = true)
    @test uses_tables(inb)
    @test call(inb, zeros(40), pv) == call(ex, zeros(40), pv)
end

@testset "output aliasing an input" begin
    # Every element is evaluated before the first write.
    @syms q[1:40]::Real
    elems = Any[i == 40 ? q[1] + q[2] : 4.0 for i in 1:40]
    ex = Code.fast_toexpr(Func([q], [], SetArray(false, q, elems, true)), IRStructure{SymReal}(), Dict{Any, Any}())
    @test uses_tables(ex)
    v = collect(1.0:40.0)
    @test call(ex, v) === v
    @test v == [fill(4.0, 39); 3.0]
end

@testset "helpers" begin
    @test Code.consecutive_runs(Int[]) == UnitRange{Int}[]
    @test Code.consecutive_runs([1, 2, 3, 7, 9, 10]) == [1:3, 7:7, 9:10]
    buf = zeros(Int, 10)
    Code.fill_constant_runs!(buf, 2.0, [2:3, 9:10], false)
    @test buf == [0, 2, 2, 0, 0, 0, 0, 0, 2, 2]
    # An `Array` is filled over the whole span, anything else only where the value goes.
    Code.fill_constant_span!(buf, 5, 1:10, [1:2], false)
    @test all(==(5), buf)
    vw = view(buf, :)
    Code.fill_constant_span!(vw, 6, 1:10, [1:2], false)
    @test buf == [6; 6; fill(5, 8)]
    @test_throws BoundsError Code.fill_constant_span!(buf, 2, 1:11, [1:11], false)
    @test_throws BoundsError Code.fill_constant_runs!(buf, 2.0, [9:11], false)
    @test_throws BoundsError Code.fill_constant_at!(buf, 2.0, [0], false)
    @test_throws BoundsError Code.set_constants!(buf, [1, 2], [1, 11], false)
    @test_throws InexactError Code.set_constants!(buf, [1.5], [1], false)
end
