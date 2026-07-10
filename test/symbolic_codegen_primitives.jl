using SymbolicUtils, SymbolicUtils.Code
using SymbolicUtils: IRStructure, SymReal, ShapeVecT, FnType
using Test

test_repr(a, b) = @test repr(Base.remove_linenums!(a)) == repr(Base.remove_linenums!(b))

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

@testset "`symAssignment` with `x(t)` lhs does not generate function" begin
    @syms t::Real x(t)::Real
    asgn = Code.symAssignment(x(t), t + 1)
    ir = IRStructure{SymReal}()
    expr = Code.fast_toexpr(asgn, ir, Dict{Any, Any}(:readable_variables => true))
    test_repr(
        expr, quote
            var"##cse#0" = (var"x(t)" = begin
                var"##cse#0" = 1
                var"##cse#1" = t
                var"##cse#2" = $(+)(var"##cse#0", var"##cse#1")
            end)
        end
    )
end

@testset "`promote_symtype` for `Let`" begin
    @test SymbolicUtils.promote_symtype(Code.Let, Real) == Real
    @test SymbolicUtils.promote_symtype(Code.Let, Real, Float64) == Float64
    @test SymbolicUtils.promote_symtype(Code.Let, Real, Real, Vector{Real}) == Vector{Real}
end

@testset "`symLet` construction" begin
    @syms x::Real y::Real z::Real
    asgn = Code.symAssignment(x, y + 1)
    l = Code.symLet([asgn], x * z)
    @test SymbolicUtils.iscall(l)
    @test SymbolicUtils.operation(l) === Code.Let
    args = SymbolicUtils.arguments(l)
    @test length(args) == 2
    @test isequal(args[1], asgn)
    @test isequal(args[2], x * z)
    @test SymbolicUtils.symtype(l) == Real
    @test SymbolicUtils.shape(l) == ShapeVecT()

    # Empty assignments — body type propagates
    l_empty = Code.symLet(typeof(x)[], x + y)
    @test SymbolicUtils.symtype(l_empty) == Real
    @test length(SymbolicUtils.arguments(l_empty)) == 1
end

@testset "`symLet` codegen — single assignment" begin
    @syms x::Real y::Real
    # let x = y + 1; x * 2 end  →  (y+1)*2
    l = Code.symLet([Code.symAssignment(x, y + 1)], x * 2)
    ir = IRStructure{SymReal}()
    expr = Code.fast_toexpr(l, ir, Dict{Any,Any}())
    result = eval(quote
        let x = 0.0, y = 3.0
            $expr
        end
    end)
    @test result ≈ 8.0   # (3+1)*2
end

@testset "`symLet` codegen — sequential assignments" begin
    @syms x::Real y::Real z::Real
    # let x = y + 1; z = x * 2; z + x end  →  ((y+1)*2) + (y+1)
    asgn1 = Code.symAssignment(x, y + 1)
    asgn2 = Code.symAssignment(z, x * 2)
    l = Code.symLet([asgn1, asgn2], z + x)
    ir = IRStructure{SymReal}()
    expr = Code.fast_toexpr(l, ir, Dict{Any,Any}())
    result = eval(quote
        let x = 0.0, y = 3.0, z = 0.0
            $expr
        end
    end)
    @test result ≈ 12.0  # (3+1)*2 + (3+1) = 8 + 4
end

@testset "`symLet` codegen — empty assignments" begin
    @syms x::Real y::Real
    l = Code.symLet(typeof(x)[], x + y)
    ir = IRStructure{SymReal}()
    expr = Code.fast_toexpr(l, ir, Dict{Any,Any}())
    result = eval(quote
        let x = 3.0, y = 4.0
            $expr
        end
    end)
    @test result ≈ 7.0
end

@testset "Self-referential assignment inside `symLet`" begin
    @syms x::Real y::Real
    l = Code.symLet([Code.symAssignment(x, x + y)], x + y)
    ir = IRStructure{SymReal}()
    # `test_repr` won't work without `:readable_variables => true`, but that
    # also masks the codegen intricacies with self-referential assignments.
    expr = Code.fast_toexpr(l, ir, Dict{Any,Any}())
    result = eval(quote
        let x = 3.0, y = 4.0
            $expr
        end
    end)
    @test result ≈ 11.0
end

@testset "`symLet` inside `symFunc`" begin
    @syms x::Real y::Real tmp::Real
    # f(x,y) = let tmp = x+y; tmp*tmp end  →  (x+y)^2
    l = Code.symLet([Code.symAssignment(tmp, x + y)], tmp * tmp)
    f = Code.symFunc([x, y], l)
    @test SymbolicUtils.symtype(f) == FnType{Tuple{Real,Real}, Real, Nothing}
    ir = IRStructure{SymReal}()
    expr = Code.fast_toexpr(f, ir, Dict{Any,Any}())
    fn = eval(expr)
    @test fn(2.0, 3.0) ≈ 25.0
    @test fn(1.0, 0.0) ≈ 1.0
end

@testset "`promote_symtype` for `DestructuredArgs`" begin
    @test SymbolicUtils.promote_symtype(Code.DestructuredArgs, Vector{Real}) == Vector{Real}
    @test SymbolicUtils.promote_symtype(Code.DestructuredArgs, Vector{Real}, Real, Real) == Vector{Real}
end

@testset "`symDestructuredArgs` construction" begin
    @syms arr[1:2]::Real x::Real y::Real
    da = Code.symDestructuredArgs(arr, [x, y])
    @test SymbolicUtils.iscall(da)
    @test SymbolicUtils.operation(da) === Code.DestructuredArgs
    args = SymbolicUtils.arguments(da)
    @test length(args) == 3
    @test isequal(args[1], arr)
    @test isequal(args[2], x)
    @test isequal(args[3], y)
    @test SymbolicUtils.symtype(da) == SymbolicUtils.symtype(arr)
    @test SymbolicUtils.shape(da) == SymbolicUtils.shape(arr)
end

@testset "`symDestructuredArgs` in `symFunc` — basic destructuring" begin
    @syms arr[1:2]::Real x::Real y::Real
    da = Code.symDestructuredArgs(arr, [x, y])
    f = Code.symFunc([da], x + y)
    @test SymbolicUtils.symtype(f) == FnType{Tuple{Vector{Real}}, Real, Nothing}
    ir = IRStructure{SymReal}()
    expr = Code.fast_toexpr(f, ir, Dict{Any,Any}())
    fn = eval(expr)
    @test fn([3.0, 4.0]) ≈ 7.0
    @test fn([1.0, -1.0]) ≈ 0.0
end

@testset "`symDestructuredArgs` in `symFunc` — mixed with plain args" begin
    # f(x, arr) = x + arr[1] + arr[2]
    @syms arr[1:2]::Real x::Real a::Real b::Real
    da = Code.symDestructuredArgs(arr, [a, b])
    f = Code.symFunc([x, da], x + a + b)
    @test SymbolicUtils.symtype(f) == FnType{Tuple{Real, Vector{Real}}, Real, Nothing}
    ir = IRStructure{SymReal}()
    expr = Code.fast_toexpr(f, ir, Dict{Any,Any}())
    fn = eval(expr)
    @test fn(1.0, [2.0, 3.0]) ≈ 6.0
    @test fn(10.0, [0.0, -5.0]) ≈ 5.0
end

@testset "`symDestructuredArgs` rewrites restored after `symFunc`" begin
    @syms arr[1:2]::Real x::Real y::Real
    da = Code.symDestructuredArgs(arr, [x, y])
    f = Code.symFunc([da], x + y)
    rewrites = Dict{Any,Any}()
    ir1 = IRStructure{SymReal}()
    Code.fast_toexpr(f, ir1, rewrites)   # must not leave arr, x, y in rewrites
    ir2 = IRStructure{SymReal}()
    expr_xy = Code.fast_toexpr(x + y, ir2, rewrites)
    result = eval(quote
        let x = 3.0, y = 4.0
            $expr_xy
        end
    end)
    @test result ≈ 7.0
end
