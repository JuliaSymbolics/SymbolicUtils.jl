using SymbolicUtils
using Test

using SymbolicUtils: showraw

const leaf_funcs = [()->100*randn(),
                    ()->rand(-100:100),
                    ()->rand(@vars a b c d e f),
                    ()->rand(@vars a b c d e f)]

const fns = vcat(1 .=> SymbolicUtils.monadic,
                 2 .=> vcat(SymbolicUtils.diadic, fill(+, 5), [-,-], fill(*, 5)),
                 3 .=> [+, *])


function gen_rand_expr(inputs; leaf_prob=0.92, depth=0, min_depth=1, max_depth=5)
    if depth > max_depth  || (min_depth <= depth && rand() < leaf_prob)
        leaf = rand(leaf_funcs)()
        if leaf isa SymbolicUtils.Variable
            @show leaf
            push!(inputs, leaf)
        end
        return leaf
    end
    arity, f = rand(fns)
    args = [gen_rand_expr(inputs,
                          leaf_prob=leaf_prob,
                          depth=depth+1,
                          min_depth=min_depth,
                          max_depth=max_depth) for i in 1:arity]
    return try
        f(args...)
    catch err
        if err isa DomainError
            return gen_rand_expr(inputs,
                                 leaf_prob=leaf_prob,
                                 depth=depth,
                                 min_depth=min_depth,
                                 max_depth=max_depth)
        end
    end
end

struct Errored
    err
end

function fuzz_test(ntrials)
    inputs = Set()
    expr = gen_rand_expr(inputs)
    unsimplifiedstr = """
    function $(tuple(inputs...))
        $(sprint(io->showraw(io, expr)))
    end
    """

    simplifiedstr = """
    function $(tuple(inputs...))
        $(sprint(io->showraw(io, simplify(expr))))
    end
    """
    f = include_string(Main, unsimplifiedstr)
    g = include_string(Main, simplifiedstr)
    @show inputs

    for i=1:ntrials
        args = [randn() for j in 1:length(inputs)]
        #unsimplified = try
            f(args...)
        #catch err
        #    Errored(err)
        #end

        simplified  = try
            g(args...)
        catch err
            Errored(err)
        end

        if unsimplified isa Errored
            @test typeof(simplified.err) == typeof(unsimplified.err)
        else
            if unsimplified ≈ simplified
                @test unsimplified ≈ simplified
            else
                @test unsimplified ≈ simplified
                println("""Test failed for expression
                               $(sprint(io->showraw(io, expr)))
                           Simplified to:
                               $(sprint(io->showraw(io, simplify(expr))))
                           On inputs:
                               $inputs = $args
                           """)
            end
        end
    end
end
