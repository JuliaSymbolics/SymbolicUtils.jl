using BenchmarkTools, SymbolicUtils
using SymbolicUtils: isnumber

using Random

SUITE = BenchmarkGroup()

@syms a b c d; Random.seed!(123);

let r = @rule(~x => ~x), rs = RuleSet([r]),
    acr = @rule(~x::isnumber + ~y => ~y)

    overhead = SUITE["overhead"]  = BenchmarkGroup()
    overhead["rule"]  = BenchmarkGroup()

    overhead["rule"]["noop:Int"]  = @benchmarkable $r(1)
    overhead["rule"]["noop:Sym"]  = @benchmarkable $r($a)
    overhead["rule"]["noop:Term"] = @benchmarkable $r($(a+2))

    overhead["acrule"]  = BenchmarkGroup()
    overhead["acrule"]["noop:Int"]  = @benchmarkable $acr(1)
    overhead["acrule"]["noop:Sym"]  = @benchmarkable $acr($a)
    overhead["acrule"]["a+2"] = @benchmarkable $acr($(a+2))
    overhead["acrule"]["a+b"] = @benchmarkable $acr($(a+b))
    overhead["acrule"]["a+2+b"] = @benchmarkable $acr($(a+2+b))

    overhead["ruleset"]  = BenchmarkGroup()
    overhead["ruleset"]["noop:Int"]  = @benchmarkable $rs(1)
    overhead["ruleset"]["noop:Sym"]  = @benchmarkable $rs($a)
    overhead["ruleset"]["noop:Term"] = @benchmarkable $rs($(a+2))

    overhead["simplify"]  = BenchmarkGroup()
    overhead["simplify"]["noop:Int"]  = @benchmarkable simplify(1)
    overhead["simplify"]["noop:Sym"]  = @benchmarkable simplify($a)
    overhead["simplify"]["noop:Term"] = @benchmarkable simplify($(a+2))

    overhead["simplify_no_fixp"]  = BenchmarkGroup()
    overhead["simplify_no_fixp"]["noop:Int"]  = @benchmarkable simplify(1, fixpoint=false)
    overhead["simplify_no_fixp"]["noop:Sym"]  = @benchmarkable simplify($a, fixpoint=false)
    overhead["simplify_no_fixp"]["noop:Term"] = @benchmarkable simplify($(a+2), fixpoint=false)

    function random_term(len; atoms, funs, fallback_atom=1)
        xs = rand(atoms, len)
        while length(xs) > 1
            xs = map(Iterators.partition(xs, 2)) do xy
                x = xy[1]; y = get(xy, 2, fallback_atom)
                rand(funs)(x, y)
            end
        end
        xs[]
    end
    ex = random_term(1000, atoms=[a, b, c, d, a^(-1), b^(-1), 1, 2.0], funs=[+, *])

    overhead["simplify_no_fixp"]["randterm:serial"] = @benchmarkable simplify($ex, threaded=false, fixpoint=false)
    overhead["simplify_no_fixp"]["randterm:thread"] = @benchmarkable simplify($ex, threaded=true,  fixpoint=false)
end
