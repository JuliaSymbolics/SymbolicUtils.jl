using Pkg, Test, SafeTestsets

@testset begin
    if haskey(ENV, "SU_BENCHMARK_ONLY")
        @safetestset "Benchmark" begin include("benchmark.jl") end
    else
        @safetestset "Doc" begin include("doctest.jl") end
        @safetestset "Types" begin include("types.jl") end
        @safetestset "Basics" begin include("basics.jl") end
        @safetestset "Order" begin include("order.jl") end
        @safetestset "PolyForm" begin include("polyform.jl") end
        @safetestset "Rewrite" begin include("rewrite.jl") end
        @safetestset "Rulesets" begin include("rulesets.jl") end
        @safetestset "Code" begin include("code.jl") end
        @safetestset "CSE" begin include("cse.jl") end
        @safetestset "Interface" begin include("interface.jl") end
        # Disabled until https://github.com/JuliaMath/SpecialFunctions.jl/issues/446 is fixed
        @safetestset "Fuzz" begin include("fuzz.jl") end
        @safetestset "Adjoints" begin include("adjoints.jl") end
        @safetestset "Hash Consing" begin include("hash_consing.jl") end
    end
end
