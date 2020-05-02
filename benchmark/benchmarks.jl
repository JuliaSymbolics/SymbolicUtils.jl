using BenchmarkTools, SymbolicUtils

using Random

SUITE = BenchmarkGroup()

@syms a b c
let r = @rule(~x => ~x), rs = RuleSet([r])
    rewriter_suite = SUITE["rewriter"]  = BenchmarkGroup()

    rewriter_suite["rule:noop:Int"]  = @benchmarkable $r(1)
    rewriter_suite["rule:noop:Sym"]  = @benchmarkable $r(a)
    rewriter_suite["rule:noop:Term"] = @benchmarkable $r(a+2)

    rewriter_suite["ruleset:noop:Int"]  = @benchmarkable $rs(1)
    rewriter_suite["ruleset:noop:Sym"]  = @benchmarkable $rs(a)
    rewriter_suite["ruleset:noop:Term"] = @benchmarkable $rs(a+2)
end
