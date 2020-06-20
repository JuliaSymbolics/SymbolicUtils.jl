include("fuzzlib.jl")

using Random: seed!

seed!(6174)
@testset "Fuzz test" begin
    @testset "polynormalize fuzz" begin
        for i=1:500
            fuzz_test(5, num_spec, SymbolicUtils.polynormalize; min_depth=3)
        end
    end
    @testset "num fuzz" begin
        for i=1:1500
            fuzz_test(5, num_spec)
        end
    end
    @testset "bool fuzz" for i=1:500 begin
        seed!(i)
        fuzz_test(5, bool_spec)
    end
end
end
