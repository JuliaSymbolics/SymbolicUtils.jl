using SymbolicUtils
using SymbolicUtils: unwrap_const, BasicSymbolic, vartype, Term, SymReal
using Test
include("utils.jl")

@syms a b c d x

@testset "Equality" begin
    @eqtest a == a
    @eqtest a != b
    @eqtest a*b == a*b
    @eqtest a*b != a
    @eqtest a != a*b
end

@testset "Literal Matcher" begin
    r = @rule 1 => 4
    @test r(1) === 4
    @test r(1.0) === 4
    @test r(2) === nothing
end

@testset "Slot matcher" begin
    @test @rule(~x => true)("?") === true
    @test @rule( ~x => ~x)(2) === 2
end

@testset "Term matcher" begin
    @test @rule(sin(~x) => ~x)(sin(a)) === a
    @eqtest @rule(sin(~x) => ~x)(sin(a^2)) == a^2
    @test @rule(sin(~x) => ~x)(sin(a)^2) === nothing
    @test @rule(sin(sin(~x)) => ~x)(sin(a^2)) === nothing
    @test @rule(sin(sin(~x)) => ~x)(sin(sin(a))) === a
    @test @rule(sin(~x)^2 => ~x)(sin(a)^2) === a
end

@testset "Equality matching" begin
    @test @rule((~x)^(~x) => ~x)(a^a) === a
    @test @rule((~x)^(~x) => ~x)(b^a) === nothing
    @test @rule((~x)^(~x) => ~x)(a+a) === nothing
    @eqtest @rule((~x)^(~x) => ~x)(sin(a)^sin(a)) == sin(a)
    # Nested AC: a local * match may bind slots that later fail at +, so
    # commutative_term_matcher retries remaining permutations.
    @eqtest @rule((~x*~y + ~z*~x)  => ~x * (~y+~z))(a*b + a*c) == a*(b+c)

    @test issetequal(@rule(+(~~x) => ~~x)(a + b), [a,b])
    @eqtest @rule(+(~~x) => ~~x)(term(+, a, b, c)) == [a,b,c]
    @eqtest @rule(+(~~x,~y, ~~x) => (unwrap_const.(~~x), unwrap_const(~y)))(term(+,9,8,9,type=Any)) == ([9,],8)
    @eqtest @rule(+(~~x,~y, ~~x) => (unwrap_const.(~~x), unwrap_const(~y), unwrap_const.(~~x)))(term(+,9,8,9,9,8,type=Any)) == ([9,8], 9, [9,8])
    @eqtest @rule(+(~~x,~y,~~x) => (unwrap_const.(~~x), unwrap_const(~y), unwrap_const.(~~x)))(term(+,6,type=Any)) == ([], 6, [])
end

@testset "Commutative + and *" begin
    r1 = @rule exp(sin(~x) + cos(~x)) => ~x
    # using a or x changes the order of the arguments in the call
    @test r1(exp(sin(a)+cos(a))) === a
    @test r1(exp(sin(x)+cos(x))) === x
    r2 = @rule (~x+~y)*(~z+~w)^(~m) => (~x, ~y, ~z, ~w, ~m)
    r3 = @rule (~z+~w)^(~m)*(~x+~y) => (~x, ~y, ~z, ~w, ~m)
    res1 = r2((a+b)*(x+c)^b)
    @test issetequal(res1[1:2], [a, b])
    @test issetequal(res1[3:4], [x, c])
    @test isequal(res1[5], b)
    res2 = r3((a+b)*(x+c)^b)
    @test issetequal(res2[1:2], [a, b])
    @test issetequal(res2[3:4], [x, c])
    @test isequal(res2[5], b)
    rPredicate1 = @rule ~x::(x->isa(x,Number)) + ~y => (~x, ~y)
    rPredicate2 = @rule ~y + ~x::(x->isa(x,Number)) => (~x, ~y)
    @test rPredicate1(2+x) === (2, x)
    @test rPredicate2(2+x) === (2, x)
    r5 = @rule (~y*(~z+~w))+~x => (~x, ~y, ~z, ~w)
    r6 = @rule ~x+((~z+~w)*~y) => (~x, ~y, ~z, ~w)
    res3 = r5(c*(a+b)+d)
    @test res3 === (d, c, a, b) || res3 === (d, c, b, a)
    res4 = r6(c*(a+b)+d)
    @test res4 === (d, c, a, b) || res4 === (d, c, b, a)
end

# Nested AC matching must backtrack when a continuation fails (depth-2).
@testset "Nested AC factoring backtracking" begin
    f1 = @acrule +(~x*~y, ~x*~z) => *(~x, ~y+~z)
    f2 = @acrule +(~y*~x, ~z*~x) => *(~x, ~y+~z)
    f3 = @acrule +(~x*~y, ~z*~x) => *(~x, ~y+~z)
    r = @rule ~y*~x + ~z*~x => ~x*(~y+~z)

    # Original Discourse/issue examples: shared factor in mixed positions
    @eqtest f1(a*b + b*c) == (a + c)*b
    @eqtest f2(a*b + b*c) == (a + c)*b
    @eqtest f3(a*b + b*c) == (a + c)*b

    # Factor on the left of both products
    @eqtest f1(a*b + a*c) == a*(b + c)
    @eqtest f2(a*b + a*c) == a*(b + c)
    @eqtest r(a*b + a*c) == a*(b + c)

    # Factor on the right of both products
    @eqtest f1(a*c + b*c) == (a + b)*c
    @eqtest f2(a*c + b*c) == (a + b)*c
    @eqtest r(a*c + b*c) == (a + b)*c
end

# Nested segments under non-commutative calls: order matters for dedup keys.
@testset "AC backtrack preserves nested segment order" begin
    @syms F(..)::Real G(..)::Real
    r1 = @rule F(~~y)*F(~~w) + G(~~y) => (~~y, ~~w)
    res = r1(F(a, b)*F(b, a) + G(a, b))
    @test res !== nothing
    @test isequal(collect(res[1]), [a, b])
    @test isequal(collect(res[2]), [b, a])
end

# Failing AC segment match on large products must stay cheap (no (n!)^2 search).
@testset "AC failing match stays bounded" begin
    @syms a b c d e f g h i j k l m n o
    ex = a*b*c*d*e*f*g + i*j*k*l*m*n*o
    # Warmup / compile
    simplify(a + b)
    t = @elapsed r = simplify(ex)
    @test isequal(r, ex)
    # Generous bound: on a quiet machine this is ~2s; 60s absorbs CI load noise.
    @test t < 60
end

# Several sibling fixed-arity products: backtracking budget must keep failure cheap.
@testset "AC multi-product failing match stays bounded" begin
    @syms G(..)::Real z
    xs = ntuple(i -> SymbolicUtils.Sym{SymbolicUtils.SymReal}(Symbol(:p1_, i); type = Number), 5)
    ys = ntuple(i -> SymbolicUtils.Sym{SymbolicUtils.SymReal}(Symbol(:p2_, i); type = Number), 5)
    zs = ntuple(i -> SymbolicUtils.Sym{SymbolicUtils.SymReal}(Symbol(:p3_, i); type = Number), 5)
    rule = @rule ~a*~b*~c*~d*~e + ~f*~g*~h*~i*~j + ~k*~l*~m*~n*~o + G(~a) => ~a
    ex = *(xs...) + *(ys...) + *(zs...) + G(z)
    rule(ex) # warmup
    t = @elapsed r = rule(ex)
    @test r === nothing
    # Generous bound: with COMM_BACKTRACK_BUDGET this is well under 1s when quiet.
    @test t < 30
end

# Nested Rule calls from a slot predicate must not change the outer work meter.
@testset "AC re-entrant predicate keeps work meter scoped" begin
    @syms G(..)::Real z q
    inner = @rule sin(~x) => ~x
    deltas = Int[]
    function pred_reent(x)
        before = SymbolicUtils.COMM_BT_USED[][]
        inner(q)
        push!(deltas, SymbolicUtils.COMM_BT_USED[][] - before)
        return true
    end
    S(s) = SymbolicUtils.Sym{SymbolicUtils.SymReal}(s; type = Number)
    # a=4, k=4 multi-product fail with predicate on ~s1_2 (reent1.jl shape).
    rule = @rule ~s1_1*~s1_2::pred_reent*~s1_3*~s1_4 +
                 ~s2_1*~s2_2*~s2_3*~s2_4 +
                 ~s3_1*~s3_2*~s3_3*~s3_4 +
                 ~s4_1*~s4_2*~s4_3*~s4_4 + G(~s1_1) => ~s1_1
    ex = prod(S(Symbol(:u, 1, :_, t)) for t in 1:4) +
         prod(S(Symbol(:u, 2, :_, t)) for t in 1:4) +
         prod(S(Symbol(:u, 3, :_, t)) for t in 1:4) +
         prod(S(Symbol(:u, 4, :_, t)) for t in 1:4) + G(z)
    rule(ex) # warmup
    empty!(deltas)
    t = @elapsed r = rule(ex)
    @test r === nothing
    @test !isempty(deltas)
    @test all(iszero, deltas)
    @test t < 30
end

# Fixed-arity product + failing segment siblings: work meter must bound cost.
@testset "AC fixed+segment failing match stays bounded" begin
    @syms G(..)::Real z
    S(s) = SymbolicUtils.Sym{SymbolicUtils.SymReal}(s; type = Number)
    us = [S(Symbol(:u, i)) for i in 1:5]
    ps = [S(Symbol(:p, i)) for i in 1:5]
    vs = [S(Symbol(:v, i)) for i in 1:7]
    ws = [S(Symbol(:w, i)) for i in 1:7]
    rule = @rule ~s1_1*~s1_2*~s1_3*~s1_4*~s1_5 + ~s2_1*~s2_2*~s2_3*~s2_4*~s2_5 + *(~α, ~~x) + *(~β, ~~x) + G(~s1_1) => ~s1_1
    ex = prod(us) + prod(ps) + prod(vs) + prod(ws) + G(z)
    rule(ex) # warmup
    t = @elapsed r = rule(ex)
    @test r === nothing
    # Generous bound for CI load; quiet-machine time should be near master (~0.2s).
    @test t < 30
end

@testset "where condition backtracks over AC matches (#776)" begin
    r = @rule (~x)^(~m)*(~y)^(~n) => (~m, ~n) where (~m)^(~n) == 8
    @test r(a^2*b^3) == (2, 3)
    @test r(b^2*a^3) == (2, 3)
    @test r(a^3*b^2) == (2, 3)
    @test r(a^3*b^3) === nothing

    r3 = @rule (~x)*(~y)*(~z) => (~x, ~y, ~z) where (~x === c && ~z === a)
    @eqtest r3(a*b*c) == (c, b, a)

    rsin = @rule sin((~x)^(~m)*(~y)^(~n)) => (~m, ~n) where (~m)^(~n) == 8
    @test rsin(sin(a^3*b^2)) == (2, 3)
    @test rsin(sin(a^2*b^3)) == (2, 3)

    rsum = @rule sin((~x)^(~m)*(~y)^(~n)) + ~w => (~m, ~n) where (~m)^(~n) == 8
    @test rsum(sin(a^3*b^2) + c) == (2, 3)
    @test rsum(sin(a^2*b^3) + c) == (2, 3)

    # the condition depends on a slot matched after the commutative subterm
    rmod = @rule mod((~x)^(~m)*(~y)^(~n), ~k) => (~m, ~n) where (~m)^(~n) == ~k
    @test rmod(mod(a^3*b^2, 8)) == (2, 3)
    @test rmod(mod(a^2*b^3, 8)) == (2, 3)
    @test rmod(mod(a^2*b^3, 9)) == (3, 2)

    for k in (2, 3, 4)
        rk = @rule (~x)^(~m) + (~~rest) => ~m where ~m == k
        @test rk(a^2 + b^3 + c^4 + d) == k
    end
    for v in (a, b, c)
        rv = @rule (~x)*(~~rest) => ~x where ~x === v
        @eqtest rv(a*b*c) == v
    end
end

@testset "RHS call counter is scoped per Rule call" begin
    inner = @rule sin(~x) => ~x
    deltas = Int[]
    function pred_rhs(x)
        before = SymbolicUtils.RULE_RHS_CALLS[][]
        inner(sin(x))
        push!(deltas, SymbolicUtils.RULE_RHS_CALLS[][] - before)
        return true
    end
    r = @rule (~x::pred_rhs)*(~~rest) => ~x where false
    @test r(a*b*c) === nothing
    @test !isempty(deltas)
    @test all(iszero, deltas)
end

@testset "Nested segment retries stay bounded" begin
    @syms F(..)::Real G(..)::Real
    n = 16
    calls = Ref(0)
    reject(x) = (calls[] += 1; false)
    pats = [:($G(~~$(Symbol(:a, i)), ~~$(Symbol(:b, i)))) for i in 1:n]
    ex = F(fill(G(a), n)..., a)
    r = @eval @rule $F($(pats...), ~z::$reject) => 1
    @test Base.invokelatest(r, ex) === nothing
    @test calls[] <= 2n
    calls[] = 0
    rw = @eval @rule $F($(pats...), ~z) => 1 where $reject(~z)
    @test Base.invokelatest(rw, ex) === nothing
    @test calls[] <= SymbolicUtils.COMM_BACKTRACK_BUDGET[] + 1
end

@testset "Slot matcher with default value" begin
    r_sum = @rule (~x + ~!y)^2 => ~y
    @test r_sum((a + b)^2) in Set([a, b])
    @test r_sum(b^2) === 0

    r_mult = @rule ~x * ~!y  => ~y
    @test r_mult(a * b) in Set([a, b])
    @test r_mult(a) === 1

    r_mult2 = @rule (~x * ~!y + ~z) => ~y
    # can match either `a` or `b` or coefficient of `c`
    @test r_mult2(c + a*b) in Set([1, a, b])
    @test r_mult2(c + b) === 1

    # here the "normal part" in the defslot_term_matcher is not a symbol but a tree
    r_mult3 = @rule (~!x)*(~y + ~z) => ~x
    @test r_mult3(a*(c+2)) === a
    @test r_mult3(2*(c+2)) === 2
    @test r_mult3(c+2) === 1

    r_pow = @rule (~x)^(~!m) => ~m
    @test isequal(r_pow(a^(b+1)), b+1)
    @test r_pow(a) === 1
    @test r_pow(a+1) === 1

    # here the "normal part" in the defslot_term_matcher is not a symbol but a tree
    r_pow2 = @rule (~x + ~y)^(~!m) => ~m
    @test r_pow2((a+b)^c) === c
    @test r_pow2(a+b) === 1

    r_mix = @rule (~x + (~y)*(~!c))^(~!m) => (~m, ~c)
    res =  r_mix((a + b*c)^2)
    @test res === (2, c) || res === (2, b) || res === (2, 1)
    res = r_mix((a + b*c))
    @test res === (1, c) || res === (1, b) || res === (1, 1)
    @test r_mix((a + b)) === (1, 1)

    r_more_than_two_arguments = @rule (~!a)*exp(~x)*sin(~x) => (~a, ~x)
    @test r_more_than_two_arguments(sin(x)*exp(x)) === (1, x)
    @test r_more_than_two_arguments(sin(x)*exp(x)*a) === (a, x)

    r_mixmix = @rule (~!a)*exp(~x)*sin(~!b + (~x)^2 + ~x) => (~a, ~b, ~x)
    @test r_mixmix(exp(x)*sin(1+x+x^2)*2) === (2, 1, x)
    @test r_mixmix(exp(x)*sin(x+x^2)*2) === (2, 0, x)
    @test r_mixmix(exp(x)*sin(x+x^2)) === (1, 0, x)

    # predicate checked in normal matching process
    r_predicate1 = @rule x + (~!m::(var->isa(var, Int))) => ~m
    @test r_predicate1(x+2) === 2
    @test r_predicate1(x+2.1) === nothing

    # predicate checked in defslot matching process
    r_predicate2 = @rule x + ~!m::(var->!(var===0)) => ~m
    @test r_predicate2(x+1)===1 # matches normally
    @test r_predicate2(x)===nothing # doesnt matches bc the default value is 0 and doesnt respect the predicate

    # multiple defslots with the same name
    r3 = @rule sin(~!f*~x)+cos(~!f*~x) => ~
    @test r3(sin(2x)+cos(2x))[:f]===2
    @test r3(sin(2x)+cos(x))===nothing
end

@testset "power matcher with negative exponent" begin
    r1 = @rule (~x)^(~y) => (~x, ~y) # rule with slot as exponent
    @test r1(1/a^b) === (a, -b) # uses frankestein
    @test r1(1/a^(b+2c)) === (a, -b-2c) # uses frankestein
    @test r1(1/a^2) === (a, -2) # uses opposite_sign_matcher
    @test r1(1/a) === (a, -1)

    r2 = @rule (~x)^(~y + ~z) => (~x, ~y, ~z) # rule with term as exponent
    res = r2(1/a^(b+2c))
    @test res === (a, -b, -2c) || res === (a, -2c, -b) # uses frankestein
    @test r2(1/a^3) === nothing # should use a term_matcher that flips the sign, but is not implemented

    r1defslot = @rule (~x)^(~!y) => (~x, ~y) # rule with defslot as exponent
    @test r1defslot(1/a^b) === (a, -b) # uses frankestein
    @test r1defslot(1/a^(b+2c)) === (a, -b-2c) # uses frankestein
    @test r1defslot(1/a^2) === (a, -2) # uses opposite_sign_matcher
    @test r1defslot(a) === (a, 1)

    r = @rule (~x + ~y)^(~m) => (~x, ~y, ~m) # rule to match (1/...)^(...)
    res = r((1/(a+b))^3)
    @test res === (a,b,-3) || res === (b, a, -3)
end

@testset "Return the matches dictionary" begin
    r = @rule (~x + (~y)^2) => ~
    res = r(a + b^2)
    @test isa(res, Base.ImmutableDict)
    @test res[:x] === a
    @test res[:y] === b

    r2 = @rule (~x + (~y)^(~m)) => (~) where ~m===2
    @test isa(r2(a + b^2), Base.ImmutableDict)
    @test r2(a + b^3)===nothing

    r3 = @rule (~x + (~y)^(~m)) => ~m===2 ? (~) : ~x
    @test isa(r3(a + b^2), Base.ImmutableDict)
    @test r3(a + b^3)===a
end

@testset "special power matches" begin
    r1 = @rule (~x)^(~y) => (~x, ~y)
    @test r1(exp(a)) === (ℯ, a) # uses exp_matcher
    @test r1(sqrt(a)) === (a, 1//2) # uses sqrt_matcher
end

@testset "Alternate form of special functions" begin
    rsqrt = @rule sqrt(~x) => ~x
    @test rsqrt(sqrt(x))===x
    @test rsqrt((x)^(1//2))===x

    rexp = @rule exp(~x) => ~x
    @test rexp(exp(x)) === x
    @test rexp(ℯ^x) === x
end

using SymbolicUtils: @capture

@testset "Capture form" begin

    ex = a^a

    #note that @test inserts a soft local scope (try-catch) that would gobble
    #the matches from assignment statements in @capture macro, so we call it
    #outside the test macro
    ret = @capture ex (~x)^(~x)
    @test ret
    @test @isdefined x
    @test x === a

    ex = b^a
    ret = @capture ex (~y)^(~y)
    @test !ret
    @test !(@isdefined y)

    ret = @capture (a + b) (+)(~~z)
    @test ret
    @test @isdefined z
    @test all(z .=== arguments(a + b))

    #a more typical way to use the @capture macro

    f(x) = if @capture x (~w)^(~w)
        w
    end

    @eqtest f(b^b) == b
    @test f(b+b) == nothing
end

@testset "Rewriter tweaks #548" begin
    struct MetaData end
    ex = a
    ex = setmetadata(ex, MetaData, :metadata)
    ex1 = ex + b

    @test getmetadata(sorted_arguments(ex1)[1], MetaData) == :metadata

    ex = a
    ex = setmetadata(ex, MetaData, :metadata)
    ex1 = ex * b

    @test getmetadata(sorted_arguments(ex1)[1], MetaData) == :metadata
end

@testset "callable struct heads in @rule #672" begin
    abstract type Form672 <: Number end
    struct ZeroForm672 <: Form672 end
    struct D672
        dim::Int
    end
    (op::D672)(x::BasicSymbolic) = SymbolicUtils.Term{vartype(x)}(op, Any[x]; type = Form672)
    Base.nameof(op::D672) = Symbol("d$(op.dim)")

    @syms z::Form672
    d₀rule = @rule D672(1)(D672(0)(~x)) => ZeroForm672()
    @test d₀rule(D672(1)(D672(0)(z))) == ZeroForm672()
    @test d₀rule(D672(2)(D672(1)(z))) === nothing

    k = 1
    dollar_rule = @rule D672($k)(D672(0)(~x)) => ZeroForm672()
    @test dollar_rule(D672(1)(D672(0)(z))) == ZeroForm672()
    @test dollar_rule(D672(2)(D672(0)(z))) === nothing
end

@testset "\$-interpolation in symbolic function call heads" begin
    @syms g(x)::Any a
    k = 1
    r = @rule g($k)(~y) => ~y
    ex1 = Term{SymReal}(g(1), Any[a]; type = Number)
    ex2 = Term{SymReal}(g(2), Any[a]; type = Number)
    @test r(ex1) === a
    @test r(ex2) === nothing
end

@testset "nested symbolic function call heads" begin
    @syms g(x)::Any a
    gg = Term{SymReal}(Term{SymReal}(g(1), Any[2]; type = Any), Any[a]; type = Number)
    r = @rule g(1)(2)(~y) => ~y
    @test r(gg) === a
    @test r(Term{SymReal}(Term{SymReal}(g(1), Any[3]; type = Any), Any[a]; type = Number)) === nothing

    k = 1
    k2 = 2
    r2 = @rule g($k)($k2)(~y) => ~y
    @test r2(gg) === a
    @test r2(Term{SymReal}(Term{SymReal}(g(1), Any[3]; type = Any), Any[a]; type = Number)) === nothing
end

@testset "nested callable-struct factory heads" begin
    abstract type FormFac <: Number end
    struct DFac
        dim::Int
    end
    (op::DFac)(x::BasicSymbolic) = SymbolicUtils.Term{vartype(x)}(op, Any[x]; type = FormFac)
    Base.nameof(op::DFac) = Symbol("d$(op.dim)")
    struct Fac end
    (::Fac)(i::Int) = DFac(i)
    struct Fac2
        n::Int
    end
    (f::Fac2)(i::Int) = DFac(f.n + i)

    @syms z::FormFac
    k = 1
    @test (@rule Fac()(1)(~x) => ~x)(DFac(1)(z)) === z
    @test (@rule Fac()(1)(~x) => ~x)(DFac(2)(z)) === nothing
    @test (@rule Fac()($k)(~x) => ~x)(DFac(1)(z)) === z
    @test (@rule Fac2(0)(1)(~x) => ~x)(DFac(1)(z)) === z
    @test (@rule $(Fac())(1)(~x) => ~x)(DFac(1)(z)) === z
end
