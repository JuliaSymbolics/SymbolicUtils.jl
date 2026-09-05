using SymbolicUtils, Test
using SymbolicUtils: BasicSymbolic

abstract type CollidingEqualityVariant <: SymbolicUtils.TreeReal end

# Exercise hash collisions without relying on random allocation addresses.
Base.objectid(::BasicSymbolic{CollidingEqualityVariant}) = UInt(0)

function equality_sym(::Type{T}, name; metadata = nothing) where {T}
    return SymbolicUtils.BSImpl.Sym{T}(;
        name, metadata, shape = SymbolicUtils.ShapeVecT(), type = Real,
        hash = UInt(0), hash2 = UInt(0), id = nothing
    )
end

function equality_term(f, args::Vector{BasicSymbolic{T}}) where {T}
    return SymbolicUtils.BSImpl.Term{T}(;
        f, args = SymbolicUtils.ArgsT{T}(args), metadata = nothing,
        shape = SymbolicUtils.ShapeVecT(), type = Real,
        hash = UInt(0), hash2 = UInt(0), id = nothing
    )
end

struct EqualityOperation
    compare::Function
end

Base.isequal(a::EqualityOperation, b::EqualityOperation) = a.compare()

@testset "Equality memo" begin
    @testset "Identity hash collisions" begin
        T = CollidingEqualityVariant
        x1, x2, y = [equality_sym(T, name) for name in (:x, :x, :y)]
        @test x1 !== x2
        @test objectid(x1) == objectid(x2) == objectid(y)
        for width in (0, 16)
            lhs = BasicSymbolic{T}[equality_sym(T, :x) for _ in 1:width]
            rhs = BasicSymbolic{T}[equality_sym(T, :x) for _ in 1:width]
            append!(lhs, [x1, x1])
            append!(rhs, [x2, y])
            result = isequal(equality_term(+, lhs), equality_term(+, rhs))
            @test !result
        end
    end

    @testset "Shared DAGs" begin
        for depth in (8, 16, 32)
            comparisons = Ref(0)
            f = EqualityOperation(() -> (comparisons[] += 1; true))
            g = EqualityOperation(() -> true)
            a, b = equality_sym.((SymReal,), (:x, :x))
            for _ in 1:depth
                a, b = equality_term(f, [a, a]), equality_term(g, [b, b])
            end
            @test isequal(a, b)
            @test comparisons[] == depth
            @test isequal(a, b)
            @test comparisons[] == 2depth
        end
    end

    @testset "Comparison mode" begin
        a = equality_sym(SymReal, :x)
        b = equality_sym(SymReal, :x; metadata = Base.ImmutableDict{DataType, Any}(Int, 1))
        f = EqualityOperation(
            () -> begin
                @test isequal(a, b)
                @test !SymbolicUtils.@manually_scope SymbolicUtils.COMPARE_FULL => true isequal(a, b)
                true
            end
        )
        g = EqualityOperation(() -> true)
        @test isequal(equality_term(f, [a]), equality_term(g, [b]))
    end

    @testset "Cleanup after exceptions" begin
        calls = Ref(0)
        saved = Ref{Any}()
        a, b = equality_sym.((SymReal,), (:x, :x))
        f = EqualityOperation(
            () -> begin
                calls[] += 1
                saved[] = SymbolicUtils.EQUALITY_MEMO[]
                isequal(a, b)
                error("equality failure")
            end
        )
        lhs, rhs = equality_term(f, [a]), equality_term(EqualityOperation(() -> true), [b])
        for _ in 1:2
            @test_throws ErrorException isequal(lhs, rhs)
            @test isempty(saved[].results)
            @test isempty(saved[].small)
            @test !saved[].active
        end
        @test calls[] == 2
        @test isequal(a, b)
    end

    @testset "Task isolation" begin
        shared_a, shared_b = equality_sym.((SymReal,), (:x, :x))
        for _ in 1:16
            shared_a = equality_term(identity, [shared_a, shared_a])
            shared_b = equality_term(identity, [shared_b, shared_b])
        end
        tasks = map(1:32) do _
            Threads.@spawn begin
                @test isequal(shared_a, shared_b)
                a, b = equality_sym.((SymReal,), (:x, :x))
                seen = Any[]
                f = EqualityOperation(
                    () -> begin
                        push!(seen, SymbolicUtils.EQUALITY_MEMO[])
                        yield()
                        @test SymbolicUtils.EQUALITY_MEMO[] === last(seen)
                        true
                    end
                )
                g = EqualityOperation(() -> true)
                @test isequal(equality_term(f, [a]), equality_term(g, [b]))
                only(seen)
            end
        end
        memos = fetch.(tasks)
        @test length(IdDict(memo => nothing for memo in memos)) == length(tasks)
        @test all(memo -> isempty(memo.results) && isempty(memo.small) && !memo.active, memos)
    end
end
