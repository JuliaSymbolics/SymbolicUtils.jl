using SymbolicUtils
using SymbolicUtils.Code
import SymbolicUtils as SU
using LinearAlgebra

# Enhanced CSE with pattern optimization
struct OptimizedCSEState
    base_state::CSEState
    optimization_patterns::Vector{Function}
    applied_optimizations::Vector{Tuple{String, Any}}
end

OptimizedCSEState() = OptimizedCSEState(
    CSEState(),
    [detect_and_optimize_matmul_add],
    Tuple{String, Any}[]
)

# Pattern detector for A * B + C → mul!(copy(C), A, B, 1, 1)
function detect_and_optimize_matmul_add(expr::BasicSymbolic, state::OptimizedCSEState)
    if !iscall(expr) || operation(expr) !== + || length(arguments(expr)) != 2
        return nothing
    end

    args = arguments(expr)

    # Try both orders: A*B + C and C + A*B
    for (mul_candidate, add_candidate) in [(args[1], args[2]), (args[2], args[1])]
        # Resolve CSE assignments
        resolved_mul = resolve_cse_assignment(mul_candidate, state.base_state)
        resolved_add = resolve_cse_assignment(add_candidate, state.base_state)

        if iscall(resolved_mul) && operation(resolved_mul) === *
            mul_args = arguments(resolved_mul)
            if length(mul_args) == 2
                A = resolve_cse_assignment(mul_args[1], state.base_state)
                B = resolve_cse_assignment(mul_args[2], state.base_state)
                C = resolved_add

                # Check if all are arrays with compatible shapes
                if all(x -> SU.symtype(x) <: AbstractArray, [A, B, C])
                    # Create optimized version
                    return create_optimized_matmul_add(A, B, C, expr, state)
                end
            end
        end
    end
    return nothing
end

function create_optimized_matmul_add(A, B, C, original_expr, state::OptimizedCSEState)
    T = SU.vartype(original_expr)

    # Create temporary variable for result
    temp_var_sym = gensym("optimized_result")
    temp_var = Sym{T}(temp_var_sym; type=SU.symtype(original_expr))

    # Create assignment for copying C
    copy_assignment = Assignment(temp_var, C)

    # Create mul! call: mul!(temp_var, A, B, 1, 1)
    mul_call_sym = gensym("mul_result")
    mul_call_var = Sym{T}(mul_call_sym; type=SU.symtype(original_expr))

    mul_call = Term{T}(LinearAlgebra.mul!,
        [temp_var, A, B, Const{T}(1), Const{T}(1)];
        type=SU.symtype(original_expr))

    mul_assignment = Assignment(mul_call_var, mul_call)

    # Add assignments to CSE state
    push!(state.base_state.sorted_exprs, copy_assignment)
    push!(state.base_state.sorted_exprs, mul_assignment)

    # Record the optimization
    push!(state.applied_optimizations, ("MatMul+Add → mul!", (A=A, B=B, C=C)))

    # Update visited map
    state.base_state.visited[original_expr.id] = mul_call_var

    return mul_call_var
end

# Enhanced CSE function with pattern optimization
function cse_with_optimization!(expr::BasicSymbolic{T}, state::OptimizedCSEState) where {T}
    get!(state.base_state.visited, expr.id) do
        iscall(expr) || return expr

        # Try pattern optimizations first
        for pattern_optimizer in state.optimization_patterns
            result = pattern_optimizer(expr, state)
            if result !== nothing
                return result
            end
        end

        # Fall back to regular CSE processing
        op = operation(expr)
        args = arguments(expr)
        cse_inside_expr(expr, op, args...) || return expr

        # Process arguments
        processed_args = map(args) do arg
            arg = unwrap_const(arg)
            if arg isa Union{Tuple, AbstractArray} &&
                (_is_array_of_symbolics(arg) || _is_tuple_of_symbolics(arg))
                # Handle array/tuple arguments (same as original CSE)
                if arg isa Tuple
                    new_arg = cse!(MakeTuple(arg), state.base_state)
                    sym = newsym!(state.base_state, T, Tuple{symtype.(arg)...})
                elseif issparse(arg)
                    new_arg = cse!(MakeSparseArray(arg), state.base_state)
                    sym = newsym!(state.base_state, T, AbstractSparseArray{symtype(eltype(arg)), indextype(arg), ndims(arg)})
                else
                    new_arg = cse!(MakeArray(arg, typeof(arg)), state.base_state)
                    sym = newsym!(state.base_state, T, AbstractArray{symtype(eltype(arg)), ndims(arg)})
                end
                push!(state.base_state.sorted_exprs, sym ← new_arg)
                state.base_state.visited[arg] = sym
                return sym
            end
            return cse_with_optimization!(arg, state)
        end

        # Create new expression with processed arguments
        new_expr = Term{T}(operation(expr), processed_args; type = symtype(expr))

        # Try optimization on the new expression
        for pattern_optimizer in state.optimization_patterns
            result = pattern_optimizer(new_expr, state)
            if result !== nothing
                return result
            end
        end

        # Standard CSE assignment
        sym = newsym!(state.base_state, T, symtype(new_expr))
        push!(state.base_state.sorted_exprs, sym ← new_expr)
        return sym
    end
end

# Helper function to run optimized CSE
function optimized_cse(expr)
    state = OptimizedCSEState()
    new_expr = cse_with_optimization!(expr, state)
    return apply_cse(new_expr, state.base_state), state
end

# Test the system
println("Testing CSE with Pattern Optimization:")
println("="^60)

@syms A[1:3, 1:3] B[1:3, 1:3] C[1:3, 1:3] D[1:3, 1:3]

# Test expressions
test_exprs = [
    A * B + C,
    A * B + C + D * A,  # Multiple patterns
    (A * B + C) + (D * A + B),  # Nested patterns
]

for (i, expr) in enumerate(test_exprs)
    println("\nTest $i: $expr")
    println("Original type: $(typeof(expr))")
    println("Original symtype: $(SU.symtype(expr))")

    # Apply optimized CSE
    optimized_expr, opt_state = optimized_cse(expr)

    println("Optimized CSE result: $optimized_expr")
    println("Number of assignments: $(length(opt_state.base_state.sorted_exprs))")

    if !isempty(opt_state.applied_optimizations)
        println("Applied optimizations:")
        for (j, (opt_name, details)) in enumerate(opt_state.applied_optimizations)
            println("  $j. $opt_name")
        end
    else
        println("No optimizations applied")
    end

    # Generate function
    func = Func([A, B, C, D], [], optimized_expr)
    code = toexpr(func)
    println("Generated code:")
    println(code)
end

println("\n" * "="^60)
println("Comparison with standard CSE:")

expr = A * B + C
println("Expression: $expr")

# Standard CSE
standard_result = cse(expr)
standard_func = Func([A, B, C], [], standard_result)
standard_code = toexpr(standard_func)

println("\nStandard CSE result:")
println(standard_code)

# Optimized CSE
optimized_result, opt_state = optimized_cse(expr)
optimized_func = Func([A, B, C], [], optimized_result)
optimized_code = toexpr(optimized_func)

println("\nOptimized CSE result:")
println(optimized_code)

println("\nOptimizations applied:")
for (opt_name, details) in opt_state.applied_optimizations
    println("- $opt_name")
end