using SymbolicUtils
using SymbolicUtils.Code
import SymbolicUtils as SU
using LinearAlgebra

# Create symbolic arrays for testing
@syms A[1:3, 1:3] B[1:3, 1:3] C[1:3, 1:3] D[1:3, 1:3]

# Define optimization templates
abstract type OptimizationTemplate end

struct MatMulAddTemplate <: OptimizationTemplate
    name::String
    pattern_detector::Function
    transformer::Function
    priority::Int
end

# Template 1: A * B + C → mul!(copy(C), A, B, 1, 1)
function detect_matmul_add(expr)
    @show "hi"
    # Check if expression is addition with exactly 2 terms
    if iscall(expr) && (operation(expr) === +) && length(arguments(expr)) == 2
        args = arguments(expr)

        # Try both orders: A*B + C and C + A*B
        for (mul_candidate, add_candidate) in [(args[1], args[2]), (args[2], args[1])]
            if iscall(mul_candidate) && operation(mul_candidate) === *
                mul_args = arguments(mul_candidate)
                if length(mul_args) == 2
                    A, B = mul_args
                    C = add_candidate

                    # Check if all are arrays with compatible shapes
                    if all(x -> SU.symtype(x) <: AbstractArray, [A, B, C])
                        A_shape = SU.shape(A)
                        B_shape = SU.shape(B)
                        C_shape = SU.shape(C)

                        # Verify matrix multiplication compatibility
                        if (isa.([A_shape, B_shape, C_shape], Ref(Vector)) |> all) &&
                           length.([A_shape, B_shape, C_shape]) == [2, 2, 2] |> all

                            A_rows, A_cols = A_shape[1], A_shape[2]
                            B_rows, B_cols = B_shape[1], B_shape[2]
                            C_rows, C_cols = C_shape[1], C_shape[2]

                            # Check shape compatibility: (m,k) * (k,n) + (m,n)
                            if A_cols == B_rows && A_rows == C_rows && B_cols == C_cols
                                return (detected=true, A=A, B=B, C=C, pattern="A*B + C")
                            end
                        end
                    end
                end
            end
        end
    end
    return (detected=false,)
end

function transform_matmul_add(match_result)
    A, B, C = match_result.A, match_result.B, match_result.C

    # Create a temporary variable for the result
    temp_var = gensym("temp_result")

    # Generate the optimized code using mul!
    # mul!(Y, A, B, α, β) computes Y = α*A*B + β*Y
    # We want: temp = C; mul!(temp, A, B, 1, 1) which gives temp = 1*A*B + 1*C
    return quote
        $temp_var = copy($C)  # Make a copy to avoid modifying original
        LinearAlgebra.mul!($temp_var, $A, $B, 1, 1)
        $temp_var
    end
end

matmul_add_template = MatMulAddTemplate(
    "Matrix Multiplication + Addition",
    detect_matmul_add,
    transform_matmul_add,
    10  # High priority
)

# Template 2: A * B * C + D → use BLAS gemm chains
function detect_matmul_chain_add(expr)
    if iscall(expr) && (operation(expr) === +) && length(arguments(expr)) == 2
        args = arguments(expr)

        for (chain_candidate, add_candidate) in [(args[1], args[2]), (args[2], args[1])]
            # Look for A * B * C pattern
            if iscall(chain_candidate) && operation(chain_candidate) === *
                chain_args = arguments(chain_candidate)

                # Check if it's a chain of multiplications
                if length(chain_args) == 2
                    left, right = chain_args
                    if iscall(left) && operation(left) === *
                        left_args = arguments(left)
                        if length(left_args) == 2
                            A, B = left_args
                            C = right
                            D = add_candidate

                            # Verify all are arrays
                            if all(x -> SU.symtype(x) <: AbstractArray, [A, B, C, D])
                                return (detected=true, A=A, B=B, C=C, D=D, pattern="A*B*C + D")
                            end
                        end
                    end
                end
            end
        end
    end
    return (detected=false,)
end

function transform_matmul_chain_add(match_result)
    A, B, C, D = match_result.A, match_result.B, match_result.C, match_result.D

    temp1 = gensym("temp_AB")
    temp2 = gensym("temp_result")

    return quote
        $temp1 = $A * $B          # First multiplication
        $temp2 = copy($D)         # Copy D for in-place operation
        LinearAlgebra.mul!($temp2, $temp1, $C, 1, 1)  # temp2 = temp1*C + D
        $temp2
    end
end

matmul_chain_add_template = MatMulAddTemplate(
    "Matrix Chain Multiplication + Addition",
    detect_matmul_chain_add,
    transform_matmul_chain_add,
    8
)

# Template registry
const OPTIMIZATION_TEMPLATES = [matmul_add_template, matmul_chain_add_template]

# Pattern matching engine
function find_optimization_patterns(expr)
    detected_patterns = []

    for template in OPTIMIZATION_TEMPLATES
        result = template.pattern_detector(expr)
        if result.detected
            push!(detected_patterns, (template=template, match=result))
        end
    end

    # Sort by priority (higher first)
    sort!(detected_patterns, by=x -> x.template.priority, rev=true)
    return detected_patterns
end

function apply_optimization(expr)
    patterns = find_optimization_patterns(expr)

    @show patterns
    if !isempty(patterns)
        # Apply the highest priority optimization
        best_match = patterns[1]
        template = best_match.template
        match_result = best_match.match

        println("Applying optimization: ", template.name)
        println("Pattern: ", match_result.pattern)

        return template.transformer(match_result)
    else
        println("No optimization patterns found")
        return nothing
    end
end

# Recursive pattern matching for complex expressions
function optimize_expression_recursive(expr)
    if !iscall(expr)
        return expr
    end

    # First, try to optimize this expression directly
    optimization = apply_optimization(expr)
    if optimization !== nothing
        return optimization
    end

    # If no direct optimization, recursively optimize arguments
    op = operation(expr)
    optimized_args = map(optimize_expression_recursive, arguments(expr))

    # Reconstruct the expression with optimized arguments
    new_expr = Term{SU.vartype(expr)}(op, optimized_args; type=SU.symtype(expr))

    # Try optimization again on the reconstructed expression
    final_optimization = apply_optimization(new_expr)
    return final_optimization !== nothing ? final_optimization : new_expr
end

# Test the optimization system
println("Testing optimization pattern detection:")
println("="^60)

test_expressions = [
    A * B + C,           # Should match matmul_add
    C + A * B,           # Should match matmul_add (reversed)
    A * B * C + D,       # Should match matmul_chain_add
    A * B + C * D,       # No match (two separate multiplications)
    A + B,               # No match (just addition)
]


expr = A * B + C
# optimized = apply_optimization(expr)
optimized = SU.Code.cse(expr)

for (i, expr) in enumerate(test_expressions)
    println("\nTest $i: $expr")
    patterns = find_optimization_patterns(expr)

    if !isempty(patterns)
        for (j, pattern_match) in enumerate(patterns)
            template = pattern_match.template
            match = pattern_match.match
            println("  Match $j: $(template.name)")
            println("    Pattern: $(match.pattern)")
            println("    Priority: $(template.priority)")
        end

        # Apply optimization
        optimized = apply_optimization(expr)
        if optimized !== nothing
            println("  Optimized code:")
            println("    ", optimized)
        end
    else
        println("  No patterns detected")
    end
end

# Test with nested expressions
println("\n" * "="^60)
println("Testing recursive optimization:")

complex_expr = (A * B + C) * D + (A * B * C + D)
println("Complex expression: $complex_expr")

# This would require implementing the recursive optimization in the CSE system
# For now, just show what patterns we can detect in sub-expressions
function analyze_subexpressions(expr, level=0)
    indent = "  " * " "^level
    println(indent, "Analyzing: $expr")

    patterns = find_optimization_patterns(expr)
    if !isempty(patterns)
        for pattern_match in patterns
            template = pattern_match.template
            match = pattern_match.match
            println(indent, "  → Found: $(template.name) - $(match.pattern)")
        end
    end

    if iscall(expr) && level < 3  # Limit depth
        for arg in arguments(expr)
            analyze_subexpressions(arg, level + 1)
        end
    end
end

analyze_subexpressions(complex_expr)

println("\n" * "="^60)
println("Integration with CSE:")
println("To integrate with CSE, you would:")
println("1. Add pattern detection to the CSE pipeline")
println("2. Replace detected patterns with optimized assignments")
println("3. Update the visited map to point to optimized symbols")
println("4. Generate efficient code with BLAS calls")