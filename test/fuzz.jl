include("fuzzlib.jl")

using Random: seed!

seed!(6174)
@testset "Fuzz test" begin
    @time @testset "expand fuzz" begin
        for i=1:500
            i % 100 == 0 && @info "expand fuzz" iter=i
            fuzz_test(5, num_spec, SymbolicUtils.expand; min_depth=3)
        end
    end

    @testset "simplify_fractions fuzz" begin
        for i=1:200
            i % 100 == 0 && @info "simplify_fractions fuzz" iter=i
            fuzz_test(5, num_spec, SymbolicUtils.simplify_fractions; min_depth=3)
        end
    end

    @time @testset "num fuzz" begin
        for i=1:1500
            i % 100 == 0 && @info "num fuzz" iter=i
            fuzz_test(5, num_spec)
        end
    end
    @time @testset "bool fuzz" begin
        for i=1:500
            seed!(i)
            i % 100 == 0 && @info "bool fuzz" iter=i
            fuzz_test(5, bool_spec)
        end
    end
    @testset "fuzz addmulpow" begin
        @time for i=1:100
            fuzz_addmulpow(1)
        end
        @time for i=1:50
            fuzz_addmulpow(2)
        end
        @time for i=1:25
            fuzz_addmulpow(3)
        end
        @time for i=1:12
            fuzz_addmulpow(4)
        end
    end
end
