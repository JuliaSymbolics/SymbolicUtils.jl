using SymbolicUtils
using SymbolicUtils.Code
import SymbolicUtils as SU

# Create symbolic arrays A, B, C
@syms A[1:2, 1:2] B[1:2, 1:2] C[1:2, 1:2]

# Create expressions
expr1 = A * B + C
expr2 = A * B + A + B
expr3 = A * B * A + C

println("Original expressions:")
println("expr1: A * B + C = ", expr1)
println("expr2: A * B + A + B = ", expr2)
println()

# Apply CSE to get the IR representation
println("CSE IR representation:")
println("=" * 50)

# CSE on first expression
cse_result1 = cse(expr1)
println("CSE result for expr1:")
println("Type: ", typeof(cse_result1))
println("Result: ", cse_result1)
println()

# CSE on second expression
cse_result2 = cse(expr2)
println("CSE result for expr2:")
println("Type: ", typeof(cse_result2))
println("Result: ", cse_result2)
println()

# Get the topological sort (assignment sequence) directly
println("Topological sort (assignment sequence):")
println("=" * 50)

assignments1 = topological_sort(expr1)
println("Assignments for expr1:")
for (i, assignment) in enumerate(assignments1)
    println("  $i: ", assignment)
end
println()

assignments2 = topological_sort(expr2)
println("Assignments for expr2:")
for (i, assignment) in enumerate(assignments2)
    println("  $i: ", assignment)
end
println()

# Manual CSE state inspection
println("Manual CSE state creation:")
println("=" * 50)

# Create CSE state and process manually
state1 = CSEState()
new_expr1 = cse!(expr1, state1)
println("CSE state for expr1:")
println("  New expression: ", new_expr1)
println("  Sorted expressions (assignments):")
for (i, assignment) in enumerate(state1.sorted_exprs)
    println("    $i: ", assignment)
    if assignment isa Assignment
        println("       LHS type: ", typeof(assignment.lhs), " :: ", SymbolicUtils.symtype(assignment.lhs))
        println("       RHS type: ", typeof(assignment.rhs), " :: ", SymbolicUtils.symtype(assignment.rhs))
    end
end
println()

state2 = CSEState()
new_expr2 = cse!(expr2, state2)
println("CSE state for expr2:")
println("  New expression: ", new_expr2)
println("  Sorted expressions (assignments):")
for (i, assignment) in enumerate(state2.sorted_exprs)
    println("    $i: ", assignment)
    if assignment isa Assignment
        println("       LHS type: ", typeof(assignment.lhs), " :: ", SymbolicUtils.symtype(assignment.lhs))
        println("       RHS type: ", typeof(assignment.rhs), " :: ", SymbolicUtils.symtype(assignment.rhs))
    end
end
println()

# Convert CSE IR back to executable code
println("Converting CSE IR to executable code:")
println("=" * 50)

# Create function using CSE result
func1 = Func([A, B, C], [], cse_result1)
println("Function for CSEd expr1:")
code1 = toexpr(func1)
println(code1)
println()

func2 = Func([A, B, C], [], cse_result2)
println("Function for CSEd expr2:")
code2 = toexpr(func2)
println(code2)
println()

# Test execution
println("Testing execution:")
println("=" * 50)

# Compile functions
compiled_func1 = eval(code1)
compiled_func2 = eval(code2)

# Test data
test_A = [1.0 2.0; 3.0 4.0]
test_B = [5.0 6.0; 7.0 8.0]
test_C = [0.1 0.2; 0.3 0.4]

result1 = compiled_func1(test_A, test_B, test_C)
result2 = compiled_func2(test_A, test_B, test_C)

println("Test inputs:")
println("A = ", test_A)
println("B = ", test_B)
println("C = ", test_C)
println()

println("Results:")
println("CSE func1 result: ", result1)
println("Direct A*B + C:   ", test_A * test_B + test_C)
println("Match: ", result1 ≈ test_A * test_B + test_C)
println()

println("CSE func2 result: ", result2)
println("Direct A*B + A + B: ", test_A * test_B + test_A + test_B)
println("Match: ", result2 ≈ test_A * test_B + test_A + test_B)