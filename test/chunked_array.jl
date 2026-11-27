using Test, SymbolicUtils
using SymbolicUtils.Code
using SymbolicUtils: Const, Sym, SymReal
using SparseArrays
using RuntimeGeneratedFunctions
RuntimeGeneratedFunctions.init(@__MODULE__)

const NV = 12
xs = [Sym{SymReal}(Symbol(:chunk_x, i); type = Real) for i in 1:NV]
zero_lit(v) = Const{SymReal}(v)

# A banded NV x NV matrix with literal zeros elsewhere. Neighbouring entries share
# subexpressions so that `cse` introduces temporaries.
function banded(; zero_elem = zero_lit(0))
    M = Matrix{SymbolicUtils.BasicSymbolic{SymReal}}(undef, NV, NV)
    for j in 1:NV, i in 1:NV
        M[i, j] = abs(i - j) > 1 ? zero_elem :
                  (xs[i] + xs[mod1(i + 1, NV)])^2 - 2 * xs[j] + 3
    end
    M
end

# Numbers with nothing but a constructor and no `zero` or promotion rules.
struct RawNumber <: Real
    v::Int
    RawNumber(v, ::Val{:raw}) = new(v)
end

function compile(body, proto = nothing)
    args = Any[DestructuredArgs(xs, :arg; create_bindings = false)]
    proto === nothing || push!(args, :proto)
    return eval(toexpr(Func(args, [], body)))
end

# `similarto` given as a runtime value keeps the unchunked `create_array` call, which is the reference.
function reference(elems, proto; cse = false)
    body = MakeArray(elems, :proto)
    f = compile(cse ? Code.cse(body) : body, proto)
    return x -> f(x, proto)
end
chunked(elems, similarto; cse = false) = compile(cse ? Code.cse(MakeArray(elems, similarto)) : MakeArray(elems, similarto))

same(a, b) = typeof(a) == typeof(b) && size(a) == size(b) && isequal(a, b)

function max_call_args(ex)
    ex isa Expr || return 0
    return max(ex.head === :call ? length(ex.args) : 0, maximum(max_call_args, ex.args; init = 0))
end

inputs = (rand(NV), rand(Float32, NV), rand(1:5, NV), rand(ComplexF64, NV),
          Rational{Int}[i // 3 for i in 1:NV], big.(rand(NV)))

@testset "chunked MakeArray" begin
    @test Code.CHUNKED_ARRAY_MIN_ELEMS <= NV^2
    @testset "dense matrix, $(cse ? "cse" : "no cse")" for cse in (false, true)
        elems = banded()
        ref = reference(elems, Matrix{Float64}(undef, 0, 0); cse)
        f = chunked(elems, Array; cse)
        for x in inputs
            @test same(@invokelatest(f(x)), @invokelatest(ref(x)))
        end
    end

    @testset "sparse-style vector of non-zeros, $(cse ? "cse" : "no cse")" for cse in (false, true)
        elems = [(xs[mod1(i, NV)] + xs[mod1(i + 1, NV)])^2 + sin(xs[mod1(i + 2, NV)]) for i in 1:200]
        ref = reference(elems, Vector{Float64}(undef, 0); cse)
        f = chunked(elems, Vector{Float64}; cse)
        for x in inputs
            x isa Vector{Rational{Int}} && continue # `sin` is not defined on rationals
            @test same(@invokelatest(f(x)), @invokelatest(ref(x)))
        end
    end

    @testset "inferred element type" begin
        f = chunked(banded(), Array)
        rt = Base.return_types(f, Tuple{Vector{Float64}}; world = Base.get_world_counter())
        @test rt == [Matrix{Float64}]
    end

    @testset "the cse case has temporaries" begin
        body = Code.cse(MakeArray(banded(), Array))
        @test body isa Let && !isempty(body.pairs)
    end

    @testset "literal zeros" begin
        # A literal `0.0` widens the element type exactly as in the unchunked call.
        elems = banded(zero_elem = zero_lit(0.0))
        ref = reference(elems, Matrix{Float64}(undef, 0, 0))
        f = chunked(elems, Array)
        for x in inputs
            @test same(@invokelatest(f(x)), @invokelatest(ref(x)))
        end
        @test eltype(@invokelatest(f(inputs[3]))) == Float64

        # `-0.0` is not `isequal` to `0.0`, so it is kept with its sign.
        elems = banded()
        elems[1, 5] = zero_lit(-0.0)
        ref = reference(elems, Matrix{Float64}(undef, 0, 0))
        f = chunked(elems, Array)
        for x in inputs
            @test same(@invokelatest(f(x)), @invokelatest(ref(x)))
        end
        @test @invokelatest(f(inputs[1]))[1, 5] === -0.0
        @test @invokelatest(f(inputs[3]))[1, 5] === -0.0

        # An array of only literals.
        allzero = fill(zero_lit(0), NV, NV)
        fz = chunked(allzero, Array)
        @test same(@invokelatest(fz(inputs[1])), zeros(Int, NV, NV))
    end

    @testset "element type is promoted from all the elements" begin
        # A chunk holding only `-1` and `UInt(1)` would be a `Vector{UInt}` on its own.
        elems = Number[-1, UInt(1), fill(1, 61)..., 0.0]
        ref = reference(elems, Vector{Float64}(undef, 0))
        f = chunked(elems, Vector{Float64})
        @test same(@invokelatest(f(inputs[1])), @invokelatest(ref(inputs[1])))
        @test @invokelatest(f(inputs[1]))[1] === -1.0

        # Int and Float32 in one chunk, Float64 elsewhere: no intermediate rounding.
        big = typemax(Int) - 1
        elems = Number[big, 1.5f0, fill(1, 98)..., 2.5, fill(3, 61)...]
        ref = reference(elems, Vector{Float64}(undef, 0))
        f = chunked(elems, Vector{Float64})
        @test same(@invokelatest(f(inputs[1])), @invokelatest(ref(inputs[1])))
    end

    @testset "per-value state of literal zeros is kept" begin
        precise = zero_lit(BigFloat(0; precision = 80))
        elems = fill(precise, NV, NV)
        f = chunked(elems, Array)
        res = @invokelatest f(inputs[1])
        @test eltype(res) == BigFloat
        @test all(z -> precision(z) == 80, res)

        # Zeros that are filled in are not aliased when the element type is mutable.
        res = @invokelatest chunked(banded(), Array)(inputs[6])
        @test eltype(res) == BigFloat
        @test res[1, NV] !== res[2, NV]
    end

    @testset "user-defined numbers" begin
        raw = RawNumber(1, Val(:raw))
        for elems in (Number[fill(raw, 64)...], Number[0.0, fill(raw, 63)...])
            ref = reference(elems, Vector{Any}(undef, 0))
            f = chunked(elems, Vector{Any})
            res = @invokelatest f(inputs[1])
            @test same(res, @invokelatest(ref(inputs[1])))
            @test res[1] === elems[1]
        end
    end

    @testset "caller bindings named like the names used by the generated code" begin
        v = [Sym{SymReal}(n; type = Real) for n in (:undef, :__values, :__array_chunk_1)]
        body = MakeTuple([MakeArray(fill(sum(v), 64), Array), v...])
        f = eval(toexpr(Func(v, [], body)))
        res = @invokelatest f(1.0, 2.0, 3.0)
        @test res[1] == fill(6.0, 64)
        @test res[2:4] == (1.0, 2.0, 3.0)
    end

    @testset "a few literal zeros are emitted, not filled" begin
        elems = [xs[mod1(i, NV)] + i for i in 1:NV^2]
        elems[7] = zero_lit(0)
        ex = string(toexpr(MakeArray(elems, Array)))
        @test !occursin("_filled_array", ex)
        ref = reference(elems, Vector{Float64}(undef, 0))
        f = chunked(elems, Vector{Float64})
        for x in inputs
            @test same(@invokelatest(f(x)), @invokelatest(ref(x)))
        end
    end

    @testset "no local functions, so closure-free compilation works" begin
        function has_closure(ex)
            ex isa Expr || return false
            ex.head in (:function, :->) && return true
            return any(has_closure, ex.args)
        end
        ex = toexpr(Func([DestructuredArgs(xs, :arg; create_bindings = false)], [], MakeArray(banded(), Array)))
        @test !has_closure(toexpr(MakeArray(banded(), Array)))
        f = RuntimeGeneratedFunction(@__MODULE__, @__MODULE__, ex; opaque_closures = false)
        @test same(@invokelatest(f(inputs[1])), @invokelatest(chunked(banded(), Array)(inputs[1])))
    end

    @testset "an irrational literal keeps the single call" begin
        # `pi` promotes with `Int` to `Float64` but with `Float32` to `Float32`, so the element
        # type depends on the order of the elements and on the Julia version.
        elems = Number[1, pi, fill(1.0f0, 62)...]
        @test max_call_args(toexpr(MakeArray(elems, Array))) > length(elems)
        ref = reference(elems, Vector{Float64}(undef, 0))
        f = chunked(elems, Vector)
        @test same(@invokelatest(f(inputs[1])), @invokelatest(ref(inputs[1])))
    end

    @testset "fresh array on every call" begin
        f = chunked(banded(), Array)
        x = inputs[1]
        a = @invokelatest f(x)
        expected = copy(a)
        fill!(a, 0.0)
        @test @invokelatest(f(x)) == expected
        @test @invokelatest(f(x)) !== @invokelatest(f(x))
    end

    @testset "no call with an argument per element" begin
        elems = banded()
        ex = toexpr(MakeArray(elems, Array))
        @test max_call_args(ex) <= Code.ARRAY_CHUNK_SIZE + 8
        # Below the threshold, the call is unchanged.
        small = toexpr(MakeArray(elems[1:4, 1:4], Array))
        @test max_call_args(small) == 5 + length(elems[1:4, 1:4])
        # Other array types and fixed element types keep the single call.
        @test max_call_args(toexpr(MakeArray(elems, Array, Float64))) > length(elems)
        @test max_call_args(toexpr(MakeArray(elems, :proto))) > length(elems)
    end
end
