using SymbolicUtils, SymbolicUtils.Code
using SymbolicUtils: IRStructure, SymReal, ShapeVecT, FnType
using Test

@testset "`symFunc` construction" begin
    @syms x::Real y::Real

    # Scalar body: type and shape
    f = Code.symFunc([x, y], x + y)
    @test SymbolicUtils.iscall(f)
    @test SymbolicUtils.operation(f) === Code.Func
    args_t, body_t = SymbolicUtils.arguments(f)
    @test SymbolicUtils.operation(args_t) === tuple
    @test SymbolicUtils.symtype(f) == FnType{Tuple{Real, Real}, Real, Nothing}
    @test SymbolicUtils.shape(f) == ShapeVecT()

    # Array body: shape propagates from body
    @syms A::AbstractMatrix{Real}
    body_arr = A * [x, y]
    f_arr = Code.symFunc([x, y], body_arr)
    @test SymbolicUtils.symtype(f_arr) == FnType{Tuple{Real, Real}, Vector{Real}, Nothing}
    @test SymbolicUtils.shape(f_arr) == SymbolicUtils.shape(body_arr)
end

@testset "`symFunc` codegen — scalar body" begin
    @syms x::Real y::Real
    f = Code.symFunc([x, y], x + y)
    ir = IRStructure{SymReal}()
    expr = Code.fast_toexpr(f, ir, Dict{Any,Any}())
    fn = eval(expr)
    @test fn(3.0, 4.0) ≈ 7.0
    @test fn(-1.0, 1.0) ≈ 0.0
end

@testset "`symFunc` codegen — array body" begin
    @syms x::Real y::Real A::AbstractMatrix{Real}
    body = A * [x, y]
    f = Code.symFunc([x, y], body)
    ir = IRStructure{SymReal}()
    Av = [1.0 2.0; 3.0 4.0]
    expr = Code.fast_toexpr(f, ir, Dict{Any,Any}())
    fn = eval(quote
        let A = $Av
            $expr
        end
    end)
    @test fn(1.0, 2.0) ≈ [5.0, 11.0]
    @test fn(0.0, 1.0) ≈ [2.0, 4.0]
end

@testset "`symFunc` CSE — body shared with outer expression" begin
    @syms x::Real y::Real
    shared = x + y
    f = Code.symFunc([x, y], shared * shared)
    ir = IRStructure{SymReal}()
    expr = Code.fast_toexpr(f, ir, Dict{Any,Any}())
    fn = eval(expr)
    @test fn(2.0, 3.0) ≈ 25.0
end

@testset "`symFunc` rewrites restored — args usable after symFunc in shared rewrites" begin
    @syms x::Real y::Real
    f = Code.symFunc([x, y], x + y)
    # Share one rewrites dict across two fast_toexpr calls.
    # Without the fix, codegenning `f` permanently adds `x` and `y` to `rewrites`
    # as function-parameter names (only valid inside the function body). The
    # second fast_toexpr would then emit `__cse = __argₛᵧₘXXX` for `x`, so the
    # generated `x + y` expression would reference undefined names.
    rewrites = Dict{Any,Any}()
    ir1 = IRStructure{SymReal}()
    Code.fast_toexpr(f, ir1, rewrites)   # populates rewrites; must not pollute x/y entries

    ir2 = IRStructure{SymReal}()
    expr_xy = Code.fast_toexpr(x + y, ir2, rewrites)
    result = eval(quote
        let x = 3.0, y = 4.0
            $expr_xy
        end
    end)
    @test result ≈ 7.0
end

@testset "`promote_symtype` for `Assignment`" begin
    @test SymbolicUtils.promote_symtype(Code.Assignment, Real, Real) == Real
    @test SymbolicUtils.promote_symtype(Code.Assignment, Any, Float64) == Float64
    @test SymbolicUtils.promote_symtype(Code.Assignment, Any, Vector{Real}) == Vector{Real}
end

@testset "`symAssignment` construction" begin
    @syms x::Real y::Real
    asgn = Code.symAssignment(x, x + y)
    @test SymbolicUtils.iscall(asgn)
    @test SymbolicUtils.operation(asgn) === Code.Assignment
    lhs_t, rhs_t = SymbolicUtils.arguments(asgn)
    @test isequal(lhs_t, x)
    @test isequal(rhs_t, x + y)
    @test SymbolicUtils.symtype(asgn) == Real
    @test SymbolicUtils.shape(asgn) == ShapeVecT()

    # Array rhs: shape propagates from rhs
    @syms A::AbstractMatrix{Real}
    body_arr = A * [x, y]
    asgn_arr = Code.symAssignment(x, body_arr)
    @test SymbolicUtils.symtype(asgn_arr) == Vector{Real}
    @test SymbolicUtils.shape(asgn_arr) == SymbolicUtils.shape(body_arr)
end

@testset "`symAssignment` codegen — scalar rhs" begin
    @syms x::Real y::Real
    asgn = Code.symAssignment(x, x + y)
    ir = IRStructure{SymReal}()
    expr = Code.fast_toexpr(asgn, ir, Dict{Any,Any}())
    result = eval(quote
        let x = 3.0, y = 4.0
            $expr
        end
    end)
    @test result ≈ 7.0
end

@testset "`symAssignment` codegen — array rhs" begin
    @syms x::Real y::Real A::AbstractMatrix{Real}
    @syms out[1:2]::Real
    body = A * [x, y]
    asgn = Code.symAssignment(out, body)
    ir = IRStructure{SymReal}()
    Av = [1.0 2.0; 3.0 4.0]
    expr = Code.fast_toexpr(asgn, ir, Dict{Any,Any}())
    result = eval(quote
        let A = $Av, x = 1.0, y = 2.0, out = zeros(2)
            $expr
        end
    end)
    @test result ≈ [5.0, 11.0]
end

@testset "`symAssignment` inside `symFunc`" begin
    # A symAssignment inside a symFunc body: f(x,y) evaluates (x = x+y; x)
    @syms x::Real y::Real
    asgn = Code.symAssignment(x, x + y)
    f = Code.symFunc([x, y], asgn)
    @test SymbolicUtils.symtype(f) == FnType{Tuple{Real, Real}, Real, Nothing}
    ir = IRStructure{SymReal}()
    expr = Code.fast_toexpr(f, ir, Dict{Any,Any}())
    fn = eval(expr)
    @test fn(3.0, 4.0) ≈ 7.0
end

