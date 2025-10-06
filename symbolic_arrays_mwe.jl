using SymbolicUtils
using SymbolicUtils.Code
import SymbolicUtils as SU

# Create symbolic arrays A, B, C
@syms A[1:2, 1:2] B[1:2, 1:2] C[1:2, 1:2]

# Create the expression A * B + C
expr = A * B + C

expr2 = A * B + A + B

println("Expression: A * B + C")
println("Symbolic result: ", expr)
println("Expression type: ", typeof(expr))
println("Shape: ", SymbolicUtils.shape(expr))
println("Symtype: ", SymbolicUtils.symtype(expr))

# Generate function from the expression
func_expr = Func([A, B, C], [], expr)
println("\nGenerated function code:")
println(toexpr(func_expr))

# Evaluate the function with actual values
generated_func = eval(toexpr(func_expr))

# Test with some values
test_A = [1.0 2.0; 3.0 4.0]
test_B = [5.0 6.0; 7.0 8.0]  
test_C = [0.1 0.2; 0.3 0.4]

result = generated_func(test_A, test_B, test_C)
println("\nTest with:")
println("A = ", test_A)
println("B = ", test_B) 
println("C = ", test_C)
println("Result = A * B + C = ", result)

# Verify manually
manual_result = test_A * test_B + test_C
println("Manual calculation: ", manual_result)
println("Results match: ", result ≈ manual_result)

println("\n" * "="^50)
println("PATTERN DETECTION FOR A*B + C")
println("="^50)

# Function to detect A*B + C pattern in symbolic expressions
function detect_matmul_add_pattern(expr)
    # Check if expression is a tree (compound expression)
    if !iscall(expr)
        return nothing
    end
    
    # Get the operation and arguments
    op = operation(expr)
    args = arguments(expr)
    
    # Check if this is an addition
    if op == (+) && length(args) == 2
        # Check both orders: A*B + C and C + A*B
        for (mul_expr, add_expr) in [(args[1], args[2]), (args[2], args[1])]
            if iscall(mul_expr) && operation(mul_expr) == (*)
                mul_args = arguments(mul_expr)
                if length(mul_args) == 2
                    A, B = mul_args
                    C = add_expr
                    
                    # Check if all are shape-compatible arrays
                    if all(x -> SymbolicUtils.symtype(x) <: AbstractArray, [A, B, C])
                        A_shape = SymbolicUtils.shape(A)
                        B_shape = SymbolicUtils.shape(B)
                        C_shape = SymbolicUtils.shape(C)
                        
                        # Check matrix multiplication compatibility: (m,k) * (k,n) + (m,n)
                        if isa(A_shape, Vector) && isa(B_shape, Vector) && isa(C_shape, Vector) &&
                           length(A_shape) == 2 && length(B_shape) == 2 && length(C_shape) == 2
                            
                            A_rows, A_cols = A_shape[1], A_shape[2]
                            B_rows, B_cols = B_shape[1], B_shape[2]
                            C_rows, C_cols = C_shape[1], C_shape[2]
                            
                            # Check if shapes are compatible for matrix multiplication and addition
                            if A_cols == B_rows && A_rows == C_rows && B_cols == C_cols
                                return (A=A, B=B, C=C, pattern="A*B + C")
                            end
                        end
                    end
                end
            end
        end
    end
    
    return nothing
end

# Test the pattern detection
println("Testing pattern detection on: ", expr)
pattern_result = detect_matmul_add_pattern(expr)

if pattern_result !== nothing
    println("✓ Detected pattern: ", pattern_result.pattern)
    println("  A = ", pattern_result.A)
    println("  B = ", pattern_result.B)
    println("  C = ", pattern_result.C)
    
    # Show shapes
    println("  Shape A: ", SymbolicUtils.shape(pattern_result.A))
    println("  Shape B: ", SymbolicUtils.shape(pattern_result.B))
    println("  Shape C: ", SymbolicUtils.shape(pattern_result.C))
else
    println("✗ Pattern not detected")
end

# Test with other expressions
println("\nTesting other expressions:")

# Test with different orderings
expr2 = C + A * B
println("\nExpression: C + A * B")
result2 = detect_matmul_add_pattern(expr2)
if result2 !== nothing
    println("✓ Detected pattern: ", result2.pattern)
else
    println("✗ Pattern not detected")
end

# Test with incompatible shapes
@syms D[1:3, 1:2] E[1:2, 1:3] F[1:4, 1:4]
expr3 = D * E + F  # Incompatible: (3,2)*(2,3) = (3,3) but F is (4,4)
println("\nExpression: D*E + F (incompatible shapes)")
result3 = detect_matmul_add_pattern(expr3)
if result3 !== nothing
    println("✓ Detected pattern: ", result3.pattern)
else
    println("✗ Pattern not detected (expected - shapes incompatible)")
end

# Test with compatible different shapes
@syms G[1:3, 1:4] H[1:4, 1:2] I[1:3, 1:2]
expr4 = G * H + I  # Compatible: (3,4)*(4,2) + (3,2)
println("\nExpression: G*H + I (compatible different shapes)")
result4 = detect_matmul_add_pattern(expr4)
if result4 !== nothing
    println("✓ Detected pattern: ", result4.pattern)
    println("  Shapes: G", SymbolicUtils.shape(result4.A), " * H", SymbolicUtils.shape(result4.B), " + I", SymbolicUtils.shape(result4.C))
else
    println("✗ Pattern not detected")
end