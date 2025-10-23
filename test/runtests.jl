using Pkg, Test, SafeTestsets

@testset begin
    if haskey(ENV, "SU_BENCHMARK_ONLY")
        @safetestset "Benchmark" begin include("benchmark.jl") end
    else
        if v"1.11" <= VERSION < v"1.12"
            # as of this comment, `@snoop_inference` on 1.12 has a tendency to never
            # end. I have kept a REPL going for 24 hours.
            #
            # The test is commented out because it behaves weirdly. It fails in CI,
            # fails differently in Pkg.test locally, and is fine when run as a script.
            # @safetestset "Precompilation" begin include("precompilation.jl") end
        end
        @safetestset "Basics" begin include("basics.jl") end
        @safetestset "Basics" begin include("arrayop.jl") end
        @safetestset "Order" begin include("order.jl") end
        @safetestset "PolyForm" begin include("polyform.jl") end
        @safetestset "Rewrite" begin include("rewrite.jl") end
        @safetestset "Rulesets" begin include("rulesets.jl") end
        @safetestset "Inference" begin include("inference.jl") end
        @safetestset "Code" begin include("code.jl") end
        @safetestset "CSE" begin include("cse.jl") end
        @safetestset "Interface" begin include("interface.jl") end
        # Disabled until https://github.com/JuliaMath/SpecialFunctions.jl/issues/446 is fixed
        @safetestset "Fuzz" begin include("fuzz.jl") end
        @safetestset "Adjoints" begin include("adjoints.jl") end
        @safetestset "Hash Consing" begin include("hash_consing.jl") end
        @safetestset "Cache macro" begin include("cache_macro.jl") end
        @safetestset "Recursive utilities" begin include("recursive_utils.jl") end
        @safetestset "Misc" begin include("misc.jl") end
        @safetestset "Method library" begin include("methods.jl") end

        # Optimization
        @safetestset "MatmulAdd Optimization" begin include("test_mul5_optimization.jl") end
    end
end
