include("fuzzlib.jl")

using Random: seed!

seed!(6174)
@testset "Fuzz test" begin
    @testset "expand fuzz" begin
        for i=1:500
            fuzz_test(5, num_spec, SymbolicUtils.expand; min_depth=3)
        end
    end
    @testset "num fuzz" begin
        for i=1:1500
            fuzz_test(5, num_spec)
        end
    end
    @testset "bool fuzz" begin
        for i=1:500
            seed!(i)
            fuzz_test(5, bool_spec)
        end
    end
    @testset "fuzz addmulpow" begin
        for i=1:100;
            fuzz_addmulpow(1)
        end
        for i=1:50;
            fuzz_addmulpow(2)
        end
        for i=1:25;
            fuzz_addmulpow(3)
        end
        for i=1:12;
            fuzz_addmulpow(4)
        end
    end
end
