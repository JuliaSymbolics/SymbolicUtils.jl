using SymbolicUtils
using SymbolicUtils.Code

# Create a complex symbolic expression with repeated subexpressions
@syms x::Real y::Real z::Real
@syms A[1:3, 1:3] B[1:3, 1:3] C[1:3, 1:3]

# Complex expression with common subexpressions
complex_expr = (x + y)^2 + 2*(x + y)*z + A*B + (A*B)*C + sin(x + y)

println("Complex expression with repeated subexpressions:")
println(complex_expr)
println()

# Analyze the IR structure before CSE
function analyze_ir_structure(expr, level=0)
    indent = "  " * repeat(" ", level*2)
    println(indent, "Expression: ", expr)
    println(indent, "Type: ", typeof(expr))
    println(indent, "SymType: ", SymbolicUtils.symtype(expr))

    if iscall(expr)
        println(indent, "Operation: ", operation(expr))
        println(indent, "Arguments (", length(arguments(expr)), "):")
        for (i, arg) in enumerate(arguments(expr))
            println(indent, "  Arg $i:")
            if level < 2  # Limit recursion depth
                analyze_ir_structure(arg, level + 1)
            else
                println(indent, "    ", arg, " :: ", SymbolicUtils.symtype(arg))
            end
        end
    elseif issym(expr)
        println(indent, "Symbol: ", expr)
        if haskey(expr, :shape)
            println(indent, "Shape: ", SymbolicUtils.shape(expr))
        end
    end
    println()
end

println("IR Structure Analysis (before CSE):")
println("="^60)
analyze_ir_structure(complex_expr)

# Apply CSE and analyze the result
println("Applying CSE transformation:")
println("="^60)

# Get CSE state
state = CSEState()
cse_expr = cse!(complex_expr, state)

println("CSE Result:")
println("Final expression: ", cse_expr)
println("Number of assignments: ", length(state.sorted_exprs))
println()

# Analyze each assignment in the CSE IR
println("CSE Assignment Analysis:")
println("-"^40)
for (i, assignment) in enumerate(state.sorted_exprs)
    if assignment isa Assignment
        lhs = assignment.lhs
        rhs = assignment.rhs

        println("Assignment $i: ", assignment)
        println("  LHS: ", lhs)
        println("    Type: ", typeof(lhs))
        println("    SymType: ", SymbolicUtils.symtype(lhs))
        if haskey(lhs, :shape)
            println("    Shape: ", SymbolicUtils.shape(lhs))
        end

        println("  RHS: ", rhs)
        println("    Type: ", typeof(rhs))
        println("    SymType: ", SymbolicUtils.symtype(rhs))
        if iscall(rhs)
            println("    Operation: ", operation(rhs))
            println("    Arguments: ", arguments(rhs))
        end
        println()
    end
end

# Create optimized function using CSE IR
println("Creating optimized function from CSE IR:")
println("="^60)

optimized_result = apply_cse(cse_expr, state)
func = Func([x, y, z, A, B, C], [], optimized_result)
optimized_code = toexpr(func)

println("Optimized function code:")
println(optimized_code)
println()

# Compare with direct compilation
println("Comparison with direct compilation:")
println("="^60)

direct_func = Func([x, y, z, A, B, C], [], complex_expr)
direct_code = toexpr(direct_func)

println("Direct function code:")
println(direct_code)
println()

# Test execution and performance
println("Testing execution:")
println("="^60)

# Compile both functions
optimized_f = eval(optimized_code)
direct_f = eval(direct_code)

# Test data
test_x, test_y, test_z = 1.0, 2.0, 3.0
test_A = rand(3, 3)
test_B = rand(3, 3)
test_C = rand(3, 3)

result_opt = optimized_f(test_x, test_y, test_z, test_A, test_B, test_C)
result_direct = direct_f(test_x, test_y, test_z, test_A, test_B, test_C)

println("Results match: ", result_opt ≈ result_direct)
println("Optimized result type: ", typeof(result_opt))
println("Direct result type: ", typeof(result_direct))

# Show the benefit of CSE
println("\nCSE Benefits:")
println("- Eliminated repeated computation of (x + y)")
println("- Reused A*B computation")
println("- Reduced total number of operations")
println("- Generated more efficient code with intermediate variables")

# Manual IR construction example
println("\n" * "="^60)
println("Manual CSE IR Construction Example:")
println("="^60)

# Create CSE state manually
manual_state = CSEState()

# Manually create intermediate assignments
temp1 = newsym!(manual_state, SymReal, Real)  # for (x + y)
temp2 = newsym!(manual_state, SymReal, Matrix{Float64})  # for A*B

# Add assignments
push!(manual_state.sorted_exprs, Assignment(temp1, x + y))
push!(manual_state.sorted_exprs, Assignment(temp2, A*B))

# Create final expression using intermediates
final_manual = temp1^2 + 2*temp1*z + temp2 + temp2*C + sin(temp1)

manual_result = apply_cse(final_manual, manual_state)
manual_func = Func([x, y, z, A, B, C], [], manual_result)
manual_code = toexpr(manual_func)

println("Manually constructed CSE IR code:")
println(manual_code)