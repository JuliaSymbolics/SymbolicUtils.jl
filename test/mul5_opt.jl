using SymbolicUtils
using SymbolicUtils.Code
import SymbolicUtils as SU
using LinearAlgebra
using Test

# Helper function to check if optimization was applied
function has_mul5_optimization(ir)
    if ir isa Code.Let
        return any(ir.pairs) do assignment
            rhs_expr = Code.rhs(assignment)
            if SU.iscall(rhs_expr)
                op = SU.operation(rhs_expr)
                return op === LinearAlgebra.mul!
            end
            false
        end
    end
    return false
end

# Helper function to build and evaluate both versions
function test_optimization(expr, args...)
    cse_ir = SU.Code.cse(expr)
    state = SU.Code.CSEState()
    optimized_ir = SU.mul5_cse2(cse_ir, state)

    # Check if optimization was applied
    has_optimization = has_mul5_optimization(optimized_ir)
    @test has_optimization

    f_cse_expr = Func(collect(args), [], cse_ir)
    f_cse = eval(toexpr(f_cse_expr))

    f_opt_expr = Func(collect(args), [], optimized_ir)
    f_opt = eval(toexpr(f_opt_expr))

    test_A = randn(3, 3)
    test_B = randn(3, 3)
    test_C = randn(3, 3)
    test_D = randn(3, 3)

    # Get concrete test args
    test_args = if length(args) == 3
        (test_A, test_B, test_C)
    else
        (test_A, test_B, test_C, test_D)
    end

    # Evaluate both versions
    result_cse = invokelatest(f_cse, test_args...)
    result_opt = invokelatest(f_opt, test_args...)

    # Assert correctness
    @test isapprox(result_cse, result_opt, rtol=1e-10)
end

@testset "Mul5 Optimization Tests" begin
    @syms A[1:3, 1:3] B[1:3, 1:3] C[1:3, 1:3] D[1:3, 1:3]

    expr1 = A * B + C
    test_optimization(expr1, A, B, C)

    expr2 = A * B + C + D
    test_optimization(expr2, A, B, C, D)

    expr4 = A * B + C + D + C * D
    test_optimization(expr4, A, B, C, D)

    expr5 = sin.(A * B + C + D + C * D)
    # test_optimization(expr5, A, B, C, D)
end
