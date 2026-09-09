using Test
using SymbolicUtils
using SymbolicUtils: SymReal
using TermInterface
using Base.Threads

function fresh_sum(trial; nargs = 1024)
    xs = [
        SymbolicUtils.Sym{SymReal}(Symbol(:threadsafe_args_, trial, :_, i); type = Real)
        for i in 1:nargs
    ]
    return sum(xs), xs
end

@testset "lazy arguments cache publication" begin
    expr, _ = fresh_sum(0; nargs = 32)
    first_args = arguments(expr)
    second_args = arguments(expr)
    @test isequal(collect(first_args), collect(second_args))
    @test parent(first_args) === parent(second_args)
end

@testset "concurrent first arguments access" begin
    if nthreads() == 1 && get(ENV, "SYMBOLICUTILS_ARGUMENTS_SUBPROCESS", "0") != "1"
        script = @__FILE__
        project = dirname(@__DIR__)
        cmd = addenv(
            `$(Base.julia_cmd()) --project=$project --threads=4 $script`,
            "SYMBOLICUTILS_ARGUMENTS_SUBPROCESS" => "1",
        )
        @test success(cmd)
    else
        @test nthreads() > 1
        for trial in 1:25
            expr, xs = fresh_sum(trial)
            expected = Set(xs)
            ready = Atomic{Int}(0)
            go = Atomic{Bool}(false)
            ntasks = max(8, 4 * nthreads())
            tasks = [
                @spawn begin
                    atomic_add!(ready, 1)
                    while !go[]
                        yield()
                    end
                    arguments(expr)
                end for _ in 1:ntasks
            ]
            while ready[] < ntasks
                yield()
            end
            go[] = true
            results = fetch.(tasks)
            published = parent(first(results))
            @test all(args -> parent(args) === published, results)
            @test all(length(args) == length(expected) for args in results)
            @test all(isequal(Set(args), expected) for args in results)
        end
    end
end
