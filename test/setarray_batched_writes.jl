using SymbolicUtils
using SymbolicUtils.Code
using SymbolicUtils.Code: IRStructure
using Test
import SymbolicUtils as SU

# A large `SetArray` writes its non-constant elements in batches instead of one statement each.
const NP = 16
const NOUT = 2 * Code.SETARRAY_BATCHED_WRITES_MIN
@syms p[1:NP]::Real out[1:NOUT]::Real k::Int

build(elems; inbounds = false, rewrites = Dict{Any, Any}(), args = [out, p]) =
    Code.fast_toexpr(Func(args, [], SetArray(inbounds, out, elems, true)), IRStructure{SymReal}(), rewrites)
unbatched() = Dict{Any, Any}(Code.SETARRAY_BATCHED_WRITES_KEY => false)
call(ex, args...) = Base.invokelatest(eval(ex), args...)
nbatches(ex) = count("set_elements!", string(ex))
# The number of `a[i] = v` statements in `ex`.
function indexed_assignments(ex)
    ex isa Expr || return 0
    n = sum(indexed_assignments, ex.args; init = 0)
    return n + (ex.head === :(=) && Meta.isexpr(ex.args[1], :ref))
end

pv = collect(1.0:NP)
elem(i) = p[mod1(i, NP)] * p[mod1(3i, NP)] + i
elemv(i) = pv[mod1(i, NP)] * pv[mod1(3i, NP)] + i

@testset "batched" begin
    n = Code.SETARRAY_BATCHED_WRITES_MIN + 37
    elems = Any[elem(i) for i in 1:n]
    expected = [elemv(i) for i in 1:n]
    ex = build(elems)
    @test nbatches(ex) == cld(n, Code.SETARRAY_BATCH_SIZE)
    @test indexed_assignments(ex) == 0
    # The statement that keeps Julia's escape analysis from running on the function.
    @test occursin("donotdelete", string(ex))
    @test call(ex, fill(NaN, NOUT), pv)[1:n] == expected
    ref = build(elems; rewrites = unbatched())
    @test nbatches(ref) == 0 && indexed_assignments(ref) == n
    @test call(ref, fill(NaN, NOUT), pv)[1:n] == expected
    inb = build(elems; inbounds = true)
    @test nbatches(inb) == nbatches(ex)
    @test call(inb, fill(NaN, NOUT), pv)[1:n] == expected
    # The writes before the one that is out of bounds happen, as for separate statements.
    for len in (n - 1, 5), e in (ex, ref)
        short = fill(NaN, len)
        @test_throws BoundsError call(e, short, pv)
        @test short == expected[1:len]
    end
    # A last batch of one element.
    m = Code.SETARRAY_BATCH_SIZE * cld(n, Code.SETARRAY_BATCH_SIZE) + 1
    one = build(Any[elem(i) for i in 1:m])
    @test nbatches(one) == cld(m, Code.SETARRAY_BATCH_SIZE)
    @test call(one, fill(NaN, NOUT), pv)[1:m] == [elemv(i) for i in 1:m]
end

@testset "output aliasing an input" begin
    # Every element is evaluated before the first write: this reverses the array in place.
    @syms q[1:NOUT]::Real
    elems = Any[q[NOUT + 1 - i] + 0 * q[i] for i in 1:NOUT]
    ex = Code.fast_toexpr(Func([q], [], SetArray(false, q, elems, true)), IRStructure{SymReal}(), Dict{Any, Any}())
    @test nbatches(ex) > 0
    v = collect(1.0:NOUT)
    @test call(ex, v) === v
    @test v == NOUT:-1:1
end

@testset "indices" begin
    n = Code.SETARRAY_BATCHED_WRITES_MIN
    # Given indices, out of order.
    elems = Any[AtIndex(NOUT - 2i + 1, elem(i)) for i in 1:n]
    ex = build(elems)
    @test nbatches(ex) > 0
    expected = zeros(NOUT)
    for i in 1:n
        expected[NOUT - 2i + 1] = elemv(i)
    end
    @test call(ex, zeros(NOUT), pv) == expected
    # The order of the writes is kept, so a repeated index is no obstacle: the last write wins.
    dup = Any[AtIndex(mod1(i, 7), elem(i)) for i in 1:n]
    ex = build(dup)
    @test nbatches(ex) > 0
    @test call(ex, zeros(NOUT), pv)[1:7] == [elemv(last(j for j in 1:n if mod1(j, 7) == i)) for i in 1:7]
    # An index that is not an integer.
    sym = Any[AtIndex(i, elem(i)) for i in 1:n]
    push!(sym, AtIndex(k, p[1]))
    @test nbatches(build(sym; args = [out, p, k])) == 0
end

@testset "not applied" begin
    n = Code.SETARRAY_BATCHED_WRITES_MIN - 1
    @test nbatches(build(Any[elem(i) for i in 1:n])) == 0
    # Elements that can only be iterated once.
    once = build(Iterators.Stateful(Any[elem(i) for i in 1:(n + 1)]))
    @test nbatches(once) == 0
    @test call(once, zeros(NOUT), pv)[1:(n + 1)] == [elemv(i) for i in 1:(n + 1)]
    # A hook on the left-hand sides has to see every write.
    hook = Dict{Any, Any}(Code.LHS_HOOK_KEY => (cs, i, lhs) -> lhs)
    @test nbatches(build(Any[elem(i) for i in 1:(n + 1)]; rewrites = hook)) == 0
    # Constants do not count: they are written from tables.
    elems = Any[isodd(i) ? 2.5 : elem(i) for i in 1:(2n)]
    ex = build(elems)
    @test nbatches(ex) == 0
    @test call(ex, zeros(NOUT), pv)[1:(2n)] == [isodd(i) ? 2.5 : elemv(i) for i in 1:(2n)]
end

@testset "with constants and other value types" begin
    n = 3 * Code.SETARRAY_BATCHED_WRITES_MIN ÷ 2
    # Every third element is a constant and every seventh an integer.
    elems = Any[i % 3 == 0 ? 0 : i % 7 == 0 ? k + i : elem(i) for i in 1:n]
    expected = Any[i % 3 == 0 ? 0 : i % 7 == 0 ? 4 + i : elemv(i) for i in 1:n]
    ex = build(elems; args = [out, p, k])
    @test nbatches(ex) > 0 && occursin("fill_constant", string(ex))
    @test call(ex, fill(NaN, NOUT), pv, 4)[1:n] == expected
    res = call(ex, Vector{Any}(undef, NOUT), pv, 4)
    ref = call(build(elems; args = [out, p, k], rewrites = unbatched()), Vector{Any}(undef, NOUT), pv, 4)
    @test all(i -> res[i] === ref[i], 1:n)
    @test res[7] === 11 && res[1] === elemv(1)
end

@testset "set_elements!" begin
    buf = zeros(4)
    @test Code.set_elements!(buf, (4, 1), false, 1.5, 2.5) === nothing
    @test buf == [2.5, 0, 0, 1.5]
    Code.set_elements!(buf, (2, 3), true, 7, 8.5)
    @test buf == [2.5, 7, 8.5, 1.5]
    @test_throws BoundsError Code.set_elements!(buf, (1, 5), false, 1.0, 2.0)
    @test buf[1] == 1.0
    @test_throws BoundsError Code.set_elements!(buf, (1, 5), false, 3, 2.0)
    @test buf[1] == 3.0
end
