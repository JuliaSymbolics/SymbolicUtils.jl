using SymbolicUtils
using SymbolicUtils: Sym, Term, symtype, shape, BasicSymbolic, Const, substitute, query, Operator, scalarize, term
import SymbolicUtils: search_variables!, default_substitute_filter, evaluate, default_is_atomic, search_variables, Code
using Test
using SparseArrays
using LinearAlgebra

@testset "Substitute with Pair" begin
    @syms x y
    result = substitute(x + y, x => 2)
    @test isequal(result, 2 + y)
end

@testset "Substitute with Array of Pairs" begin
    @syms x y z
    result = substitute(x + y + z, [x => 1, y => 2])
    @test isequal(result, 3 + z)
end

@testset "Substitute SparseMatrixCSC" begin
    @syms x
    sparse_mat = sparse([1, 2], [1, 2], [x, 2x])
    result = substitute(sparse_mat, x => 3)
    # Test that result is a sparse matrix with correct values
    @test result isa SparseMatrixCSC
    @test nnz(result) == 2  # 2 non-zero entries
end

@testset "Substitute division with can_fold" begin
    @syms x y
    expr = x / y
    # When both are constants, should fold
    result = substitute(expr, Dict(x => 10, y => 2); fold=Val(true))
    # Just test that substitute works with fold parameter
    @test result isa BasicSymbolic{SymReal}
    @test isequal(unwrap_const(result), 5)
end

@testset "Substitute with 3 args can_fold" begin
    @syms x y z
    expr = clamp(x, y, z)
    result = substitute(expr, Dict(x => 5, y => 1, z => 10); fold=Val(true))
    # Just test that substitute works with fold parameter
    @test result isa BasicSymbolic{SymReal}
    @test isequal(unwrap_const(result), 5)
end

@testset "Substitute with 4+ args can_fold" begin
    # We need a function that takes 4+ arguments
    f = (a, b, c, d) -> a + b + c + d
    @syms w x y z
    # Register the function with SymbolicUtils
    expr = Term{SymbolicUtils.SymReal}(f, [w, x, y, z]; type = Real, shape = SymbolicUtils.ShapeVecT())
    # Substitute all variables with constants
    result = substitute(expr, Dict(w => 1, x => 2, y => 3, z => 4); fold=Val(true))
    # Just test that substitute works with fold parameter
    @test result isa BasicSymbolic{SymReal}
    @test isequal(unwrap_const(result), 10)
end

@testset "Query with AddMul" begin
    @syms x y z
    # Create an expression that uses Add/Mul optimization
    expr = x + y + z
    # Query if it contains x
    has_x = query(ex -> isequal(ex, x), expr)
    @test has_x == true
end

@testset "Query with Div" begin
    @syms x y z
    expr = (x + z) / y
    # Query if it contains y
    has_y = query(ex -> isequal(ex, y), expr)
    @test has_y == true
end

@testset "Query with ArrayOp" begin
    @syms x[1:3]
    # Create an array operation
    expr = x .+ 1
    # Query if it contains any symbolic
    has_symbolic = query(isequal(x), expr)
    @test has_symbolic == true
end

@testset "search_variables! with Div" begin
    @syms x y z
    expr = (x + 2) / (y + 3)
    vars = Set{Any}()
    search_variables!(vars, expr)
    @test x in vars
    @test y in vars
    let_block = Code.cse(expr)
    let_vars = search_variables(let_block)
    @test issetequal(vars, let_vars)
end

@testset "search_variables! with ArrayOp" begin
    @syms x[1:3]
    expr = x .+ 1
    vars = Set{Any}()
    search_variables!(vars, expr)
    @test any(v -> v isa BasicSymbolic, vars)
    let_block = Code.cse(expr)
    let_vars = search_variables(let_block)
    @test issetequal(vars, let_vars)
end

@testset "search_variables! with AbstractArray" begin
    @syms x y z
    arr = [x + y, y + z, x + z]
    vars = Set{Any}()
    search_variables!(vars, arr)
    @test x in vars
    @test y in vars
    @test z in vars
    let_block = Code.cse(arr)
    let_vars = search_variables(let_block)
    @test issetequal(vars, let_vars)
end

@testset "search_variables! with SparseMatrixCSC" begin
    @syms x y
    sparse_mat = sparse([1, 2], [1, 2], [x, y])
    vars = Set{Any}()
    search_variables!(vars, sparse_mat)
    @test x in vars
    @test y in vars
    vars = search_variables(sparse_mat)
    @test x in vars
    @test y in vars
end

@testset "det scalarization" begin
    for N in 2:5
        @syms M[1:N, 1:N]
        det_expr = LinearAlgebra.det(M)

        det_scal = SymbolicUtils.scalarize(det_expr)

        vals = reshape(1:(N*N), N, N)
        @test det(vals) ≈ unwrap_const(substitute(det_scal, Dict(M => vals); fold = Val(true))) atol = 1e-16
    end
end

@testset "evaluate function" begin
    # Test lines 139-140: evaluate function
    @syms x
    expr = sin(x)
    # Substitute and evaluate
    result = evaluate(substitute(expr, Dict(x => 2)))
    @test result isa BasicSymbolic{SymReal}
    @test unwrap_const(result) ≈ sin(2.0)
end

@testset "scalarize with AbstractArray" begin
    @syms x[1:2]
    arr = [x]
    # Scalarize an array
    result = scalarize(arr)
    @test result isa Vector
    @test length(result) == 1
    @test isequal(result[1], scalarize(x))
end

@testset "scalarize with non-symbolic input" begin
    # Test that scalarize returns non-symbolic values unchanged
    result = scalarize(5)
    @test result == 5
end

@testset "scalarize with toplevel ArrayOp" begin
    @syms x[1:2, 1:2]
    # Create an ArrayOp expression
    expr = x .+ 1
    # Scalarize with toplevel=true
    result = scalarize(expr, Val{true}())
    @test result isa AbstractArray
end

@testset "scalarize with array shape expressions" begin
    @syms x[1:2]
    # Test scalarize with array expressions
    expr = x .* 2
    result = scalarize(expr)
    @test isequal(result, [2x[1], 2x[2]])
end

@testset "substitute with custom filterer" begin
    @syms x y z
    expr = x + y * z
    # Use a custom filterer that blocks certain operations
    custom_filter = !isequal(y * z)
    result = substitute(expr, Dict(z => 1); filterer=custom_filter, fold=Val(true))
    @test isequal(result, expr)
end

@testset "query with recurse parameter" begin
    @syms x y z
    expr = x + y * z
    # Query with custom recurse function
    has_z = query(ex -> isequal(ex, z), expr; recurse = x -> operation(x) !== (*))
    @test has_z == false

    result = query(ex -> false, 5)
    @test result == false
end

@testset "query with ArrayOp and term field" begin
    @syms x[1:3]
    expr = 2 .* x
    result = query(ex -> iscall(ex) && operation(ex) === broadcast, expr; default=false)
    @test result == true
end

@testset "default_is_atomic edge cases" begin
    @test !default_is_atomic(SymbolicUtils.IDXS_SYMREAL)
    @test !default_is_atomic(SymbolicUtils.IDXS_SYMREAL[1])
end

@testset "Scalarization of matmul with scalar coeff" begin
    @syms x y[1:2, 1:2] z[1:2]
    expr = x * y * z
    scal = SymbolicUtils.scalarize(expr)
    @test scal isa Vector
    @test length(scal) == 2
    truth = x .* (collect(y) * collect(z))
    @test isequal(truth, scal)
end

@testset "Scalarization of array addition" begin
    @syms x[1:3] y[1:3] z[1:3]
    expr = x + y + z
    scal = SymbolicUtils.scalarize(expr)
    @test scal isa Vector
    @test length(scal) == 3
    truth = collect(x) + collect(y) + collect(z)
    @test isequal(truth, scal)
end

@testset "Scalarization of array division" begin
    @syms x y[1:2, 1:2] z[1:2]
    expr = (y * z) / x
    scal = SymbolicUtils.scalarize(expr)
    @test scal isa Vector
    @test length(scal) == 2
    truth = [(y[1, 1] * z[1] + y[1, 2] * z[2]) / x, (y[2, 1] * z[1] + y[2, 2] * z[2]) / x]
    @test isequal(scal, truth)

    expr = x \ (y * z)
    scal = SymbolicUtils.scalarize(expr)
    @test scal isa Vector
    @test length(scal) == 2
    @test isequal(scal, truth)
end

@testset "Scalarization of ldiv" begin
    @syms x y A[1:3, 1:3] b[1:3]
    @test isequal(SymbolicUtils.scalarize(x \ y), x \ y)
    @test isequal(SymbolicUtils.scalarize(A \ b), [(A \ b)[1], (A \ b)[2], (A \ b)[3]])
end

@testset "Substitution inside large symbolic arrays" begin
    @syms a b
    arr = zeros(BasicSymbolic{SymReal}, 100, 100)
    arr[5, 5] = a
    arr = Const{SymReal}(arr)
    @test_nowarn substitute(arr, [a => b])
end

@testset "scalarize preserves deferred broadcast substitute (#494)" begin
    @syms X[1:2]::Real w::Real
    Y = substitute.(X, w => -w)
    Ys = scalarize(Y)
    @test all(y -> iscall(y) && operation(y) === substitute, Ys)
    @test all(y -> symtype(y) === Real, Ys)
    result = map(y -> substitute(y, Dict(X[1] => 2w, X[2] => 3w)), Ys)
    @test isequal(result, [-2w, -3w])

    lazy = term(substitute, X[1], w => -w; type = symtype(X[1]), shape = shape(X[1]))
    @test isequal(substitute(lazy, Dict(X[1] => 2w); fold = Val(true)), -2w)
end

@testset "Preserve already-applicable substitutions" begin
    @syms X[1:2]::Real w::Real z::Real
    @test isequal(scalarize(substitute.(X, X[1] => w)), [w, X[2]])
    for fold in (Val(false), Val(true))
        got = substitute(scalarize(substitute.(X .+ w, w => z)), Dict(w => 1); fold)
        @test isequal(got, [X[1] + z, X[2] + z])
    end
    got = scalarize(substitute(substitute.(X, w => -w), Dict(X => [2w, 3w])))
    @test isequal(got, [-2w, -3w])
end

@testset "Identity substitution keeps numeric scalar type" begin
    @syms X[1:2]::Real w::Real
    ys = scalarize(substitute.(X, w => w))
    @test symtype(ys[1]) === Real
    @test isequal(ys[1] + 1, X[1] + 1)
    @test isequal(2ys[1], 2X[1])
    @test isequal(sin(ys[1]), sin(X[1]))
end

@testset "Deferred sign-changing substitute keeps numeric type" begin
    @syms X[1:2]::Real w::Real
    ys = scalarize(substitute.(X, w => -w))
    @test all(y -> symtype(y) === Real, ys)
    @test isequal(substitute(ys[1] + 1, Dict(X[1] => 2w)), -2w + 1)
    @test isequal(substitute(2ys[1], Dict(X[1] => 2w)), -4w)
    @test isequal(substitute(sin(ys[1]), Dict(X[1] => 2w)), sin(-2w))
end

@testset "Pending substitute survives repeated scalarization" begin
    @syms X[1:2]::Real A[1:2]::Real w::Real z::Real
    ys = scalarize(substitute.(X, w => -w))
    rules = Dict(X[1] => 2w, X[2] => 3w)
    for (ex, expected) in (
            (scalarize(ys), [-2w, -3w]),
            (scalarize(scalarize(ys)), [-2w, -3w]),
            (scalarize(2ys), [-4w, -6w]),
            (scalarize(1 .+ ys), [1 - 2w, 1 - 3w]),
            (scalarize(sin.(ys)), [sin(-2w), sin(-3w)]),
            (scalarize(substitute.(substitute.(X, w => -w), w => 2w)), [-4w, -6w]),
        )
        @test isequal(substitute(ex, rules), expected)
    end
    aliased = substitute(ys, Dict(X => A))
    @test isequal(substitute(aliased, Dict(A[1] => 2w, A[2] => 3w)), [-2w, -3w])
    @test isequal(substitute(substitute(ys, Dict(z => 1)), rules), [-2w, -3w])
    @test isequal(scalarize(term(substitute, 2w, w => -w; type = Real, shape = shape(w))), -2w)
    @test_throws MethodError scalarize(substitute.(X, w => -w, 1))
end
