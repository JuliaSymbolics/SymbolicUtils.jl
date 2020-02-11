using Test
using SymbolicUtils

using SymbolicUtils: Rule, rewriter

@vars a b c

# Literal matcher
let r = rewriter(Rule(1, d->4))
    @test r(1) === 4
    @test r(1.0) === 4
    @test r(2) === nothing
end

# Slot matcher
@test rewriter(@rule ~x => true)("?") === true
@test rewriter(@rule ~x => ~x)(2) === 2

# Term matcher
@test rewriter(@rule sin(~x) => ~x)(sin(a)) === a
@test rewriter(@rule sin(~x) => ~x)(sin(a^2)) == a^2
@test rewriter(@rule sin(~x) => ~x)(sin(a)^2) === nothing
@test rewriter(@rule sin(sin(~x)) => ~x)(sin(a^2)) === nothing
@test rewriter(@rule sin(sin(~x)) => ~x)(sin(sin(a))) === a
@test rewriter(@rule sin(~x)^2 => ~x)(sin(a)^2) === a
# Equality matching
@test rewriter(@rule (~x)^(~x) => ~x)(a^a) === a
@test rewriter(@rule (~x)^(~x) => ~x)(b^a) === nothing
@test rewriter(@rule (~x)^(~x) => ~x)(a+a) === nothing
@test rewriter(@rule (~x)^(~x) => ~x)(sin(a)^sin(a)) === sin(a)

