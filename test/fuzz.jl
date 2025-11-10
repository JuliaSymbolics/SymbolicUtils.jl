include("fuzzlib.jl")

using Random: seed!

seed!(8258)
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

    @testset "fuzz StableIndex" begin
        for _ in 1:10
            axes = UnitRange{Int}[]
            nd = rand(2:5)
            for i in 1:nd
                left = rand(-5:5)
                right = rand(left:10)
                push!(axes, left:right)
            end
            axes_tup = Tuple(axes)

            for _ in 1:100
                idx = Int[]
                for i in 1:nd
                    push!(idx, rand(axes[i]))
                end
                si = SymbolicUtils.StableIndex(idx)

                cartidx = CartesianIndex(Tuple(idx))
                cart_idx_truth = findfirst(isequal(cartidx), CartesianIndices(axes_tup))
                lin_idx_truth = LinearIndices(axes_tup)[cart_idx_truth]
                lin_idx_generated = SymbolicUtils.as_linear_idx(axes_tup, si)
                lin_idx_shapevect = SymbolicUtils.as_linear_idx(SymbolicUtils.ShapeVecT(axes), si)
                if lin_idx_generated == lin_idx_truth == lin_idx_shapevect
                    @test true
                else
                    @test_broken false
                    println("""
                    Broken StableIndex test:
                    - axes: $axes
                    - idx: $idx
                    - lin_idx_truth: $lin_idx_truth
                    - lin_idx_generated: $lin_idx_generated
                    - lin_idx_shapevect: $lin_idx_shapevect
                    """)
                end
            end
        end
    end
