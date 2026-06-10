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
