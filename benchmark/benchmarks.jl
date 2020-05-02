using BenchmarkTools, SymbolicUtils

using Random

SUITE = BenchmarkGroup()

@syms a b c
let r = @rule(~x => ~x), rs = RuleSet([r])
    overhead = SUITE["overhead"]  = BenchmarkGroup()
    overhead["rule"]  = BenchmarkGroup()

    overhead["rule"]["noop:Int"]  = @benchmarkable $r(1)
    overhead["rule"]["noop:Sym"]  = @benchmarkable $r($a)
    overhead["rule"]["noop:Term"] = @benchmarkable $r($(a+2))

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
end
