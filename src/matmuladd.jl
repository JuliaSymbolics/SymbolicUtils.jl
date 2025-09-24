# Pattern-based optimization templates for CSE
struct OptimizationRule
    name::String
    detector::Function
    transformer::Function
    priority::Int
end

# Helper function to resolve assignments in CSE state
# function resolve_cse_assignment(expr::BasicSymbolic, state::CSEState)
#     if issym(expr) && haskey(state.visited, expr.id)
#         resolved = state.visited[expr.id]
#         return resolved != expr ? resolve_cse_assignment(resolved, state) : expr
#     end
#     return expr
# end



function resolve_cse_assignment(expr::BasicSymbolic, state::CSEState)
    return expr
end

function is_cse_var(x, state::CSEState)
    # return issym(expr) && haskey(state.visited, expr.id)
    @show x
    id = "##cse#"
    @show id
    @show find_cse_expr(x, state)
    @show occursin(id, string(nameof(x)))
    # return false
end

function find_cse_expr(x, state)
    idx = findfirst(y -> nameof(lhs(y)) == nameof(x), state.sorted_exprs)
    isnothing(idx) ? nothing : (; expr = rhs(state.sorted_exprs[idx]), x)
end

function detect_matmul_add_pattern(expr, state::CSEState)
    @warn expr
    @show state.sorted_exprs
    global gs = state

    # Must be addition with exactly 2 arguments
    if !iscall(expr) || (operation(expr) !== +) || length(arguments(expr)) != 2
        return nothing
    end

    args = arguments(expr)
    @show args

    if all(x -> x <: AbstractArray, symtype.(args))
        if (operation(expr) === +) && length(args) == 2
            @show expr
            # @show any(x -> is_cse_var(x, state), args)
            cse_exprs = map(x -> find_cse_expr(x, state), args)
            # if 
            @show cse_exprs
            C_idx = only(findfirst(isnothing, cse_exprs))
            var_idx = only(findfirst(!isnothing, cse_exprs))
            @show C_idx
            C = args[C_idx]
            var_ex = cse_exprs[var_idx].expr
            var_args = arguments(var_ex)
            @assert operation(var_ex) === *
            @show var_ex

            return (; A = var_args[1], B = var_args[2], C = C, original_expr = expr)
        end
    end

    # Try both orders: A*B + C and C + A*B
    # for (mul_candidate, add_candidate) in [(args[1], args[2]), (args[2], args[1])]
    #     # Resolve through CSE assignments
    #     resolved_mul = resolve_cse_assignment(mul_candidate, state)
    #     resolved_add = resolve_cse_assignment(add_candidate, state)

    #     if iscall(resolved_mul) && operation(resolved_mul) === *
    #         mul_args = arguments(resolved_mul)
    #         if length(mul_args) == 2
    #             A = resolve_cse_assignment(mul_args[1], state)
    #             B = resolve_cse_assignment(mul_args[2], state)
    #             C = resolved_add

    #             # Verify all are arrays (this is where the real pattern matching happens)
    #             if all(x -> symtype(x) <: AbstractArray, [A, B, C])
    #                 return (A=A, B=B, C=C, original_expr=expr)
    #             end
    #         end
    #     end
    # end
    return nothing
end

function transform_to_mul5_assignment(match_data, state::CSEState)
    A, B, C = match_data.A, match_data.B, match_data.C
    T = vartype(match_data.original_expr)

    # Create temporary variable for the result
    temp_var_sym = gensym("mul5_temp")
    temp_var = Sym{T}(temp_var_sym; type=symtype(match_data.original_expr))

    # Create the mul! call: mul!(copy(C), A, B, 1, 1)
    # This computes: result = 1*A*B + 1*C
    copy_call = Term{T}(copy, [C]; type=symtype(C))
    mul_call = Term{T}(LinearAlgebra.mul!,
        [temp_var, A, B, Const{T}(1), Const{T}(1)];
        type=symtype(match_data.original_expr))

    # Add assignments to CSE state
    copy_assignment = Assignment(temp_var, copy_call)
    mul_assignment = Assignment(temp_var, mul_call)  # This overwrites temp_var with mul! result

    push!(state.sorted_exprs, copy_assignment)
    push!(state.sorted_exprs, mul_assignment)

    # Update visited map
    state.visited[match_data.original_expr.id] = temp_var

    return temp_var
end

# Rule 1: A * B + C → optimized mul! version
const MATMUL_ADD_RULE = OptimizationRule(
    "MatMul+Add",
    detect_matmul_add_pattern,
    transform_to_mul5_assignment,
    10
)

# Apply optimization rules during CSE
function apply_optimization_rules(expr, state::CSEState, rules=[MATMUL_ADD_RULE])
    for rule in sort(rules, by=r->r.priority, rev=true)
        match_data = rule.detector(expr, state)
        if match_data !== nothing
            println("Applying rule: $(rule.name)")
            return rule.transformer(match_data, state)
        end
    end
    return nothing
end