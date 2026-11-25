using SymbolicUtils
using SymbolicUtils: ifelse_eager, ifelse_branching, term, symtype
using SymbolicUtils.Code
using RuntimeGeneratedFunctions
using Test

RuntimeGeneratedFunctions.init(@__MODULE__)

# Errors if it is ever actually evaluated; used to detect whether the untaken branch runs.
boom(v) = error("untaken branch was evaluated: boom($v)")
boomterm(v) = term(boom, v; type = Real, shape = SymbolicUtils.shape(v))

compile(body, args...) = @RuntimeGeneratedFunction(toexpr(cse(Func(collect(args), [], body))))

@testset "Construction, symtype and shape mirror `ifelse`" begin
    @syms cond::Bool a b x[1:3] y[1:3] z[1:4]
    for op in (ifelse_eager, ifelse_branching)
        e = op(cond, a, b)
        @test operation(e) === op
        @test symtype(e) == symtype(ifelse(cond, a, b))
        @test SymbolicUtils.promote_symtype(op, Bool, Int, Bool) == Int
        @test_throws ArgumentError SymbolicUtils.promote_symtype(op, Real, Int, Float64)
        # array-branch rules match `ifelse`
        @test SymbolicUtils.shape(op(cond, x, y)) == [1:3]
        @test_throws ErrorException op(cond, x, z)
    end
end

@testset "Lowering forms" begin
    @syms cond::Bool a b
    @test toexpr(ifelse_branching(cond, a, b)).head === :if
    # `ifelse_eager` lowers via the generic fallback to a plain (eager) call
    @test toexpr(ifelse_eager(cond, a, b)).head === :call
end

@testset "simplify folds like `ifelse`" begin
    @syms cond::Bool b
    for op in (ifelse_eager, ifelse_branching)
        @test isequal(simplify(op(cond, b, b)), b)
    end
end

@testset "ifelse_branching does not evaluate the untaken branch" begin
    @syms x::Real
    f = compile(ifelse_branching(x > 0, x^2, boomterm(x)), x)
    @test f(2.0) == 4.0          # takes the valid branch; `boom` never runs
    g = compile(ifelse_branching(x > 0, boomterm(x), 1 / x), x)
    @test g(-2.0) == -0.5
end

@testset "ifelse_eager evaluates both branches" begin
    @syms x::Real
    f = compile(ifelse_eager(x > 0, x^2, boomterm(x)), x)
    @test_throws ErrorException f(2.0)
end

# Counts how many times it is evaluated; used to detect duplicated computation.
const FIRE_COUNT = Ref(0)
fire(v) = (FIRE_COUNT[] += 1; v)
fireterm(v) = term(fire, v; type = Real, shape = SymbolicUtils.shape(v))

@testset "multiply-referenced ifelse_branching is computed once under CSE" begin
    @syms x::Real
    z = ifelse_branching(x > 0, fireterm(x)^2, boomterm(x))
    # CSE binds the conditional itself to a temporary...
    csex = cse(z + 2z)
    @test csex isa Let
    @test count(p -> p isa Assignment && iscall(p.rhs) &&
        operation(p.rhs) === ifelse_branching, csex.pairs) == 1
    # ...so referencing it twice evaluates the taken branch once and the untaken
    # branch (`boom`) not at all.
    f = compile(z + 2z, x)
    FIRE_COUNT[] = 0
    @test f(2.0) == 12.0
    @test FIRE_COUNT[] == 1

    # One-sided nesting stays linear: each level is emitted once, matching `ifelse`.
    # (A conditional referenced inside *both* branches of an enclosing one is still
    # emitted per branch — hoisting it out would evaluate it eagerly.)
    nested_b = ifelse_branching(x > 0, x, -x)
    nested_i = ifelse(x > 0, x, -x)
    for i in 1:5
        nested_b = ifelse_branching(x > i, nested_b + 1, -x)
        nested_i = ifelse(x > i, nested_i + 1, -x)
    end
    code_b = string(toexpr(cse(Func([x], [], nested_b))))
    code_i = string(toexpr(cse(Func([x], [], nested_i))))
    nif(s) = length(collect(eachmatch(r"\bif\b", s)))
    @test nif(code_b) == nif(code_i) == 6
    fb = compile(nested_b, x)
    fi = compile(nested_i, x)
    @test fb(2.5) == fi(2.5) == -2.5
end
