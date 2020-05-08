
include("fuzzlib.jl")

using Random: seed!

@testset "Fuzz test" begin
    seed!(6174)
    for i=1:1500
        fuzz_test(10, num_spec)
    end
    for i=1:500
        fuzz_test(8, bool_spec)
    end
end
