# Pattern-based optimization templates for CSE
struct OptimizationRule
    name::String
    detector::Function
    transformer::Function
    priority::Int
end

function find_cse_expr(x, state)
    idx = findfirst(y -> nameof(lhs(y)) == nameof(x), state.sorted_exprs)
    isnothing(idx) ? nothing : (; expr = rhs(state.sorted_exprs[idx]), x)
end

function validate_mul_shapes(A, B, C)
    [shape(A)[1], shape(B)[2]] == shape(C)
end

function validate_mul_shapes(A, B, C...)
    # [shape(A)[1], shape(B)[2]] == shape(first(C)) && all(x -> shape(first(C)) == shape(x), Base.tail(C))
    [shape(A)[1], shape(B)[2]] == shape(first(C))
end

function detect_matmul_add_pattern(expr::Let, state::CSEState)
    mul_candidates_idx = findall(expr.pairs) do x
        # @show typeof(rhs(x))
        # @show arguments(rhs(x))
        # @show x
        args = rhs(x) isa Const ? [] : arguments(rhs(x))
        all_arrays = all(y -> y <: AbstractArray, symtype.(args))
        is_mul = operation(rhs(x)) === *
        all_arrays && is_mul
    end
    mul_candidates = expr.pairs[mul_candidates_idx]

    plus_candidates_idx = findall(expr.pairs) do x
        all_arrays = all(y -> y <: AbstractArray, symtype.(arguments(rhs(x))))
        is_plus = operation(rhs(x)) === +
        all_arrays && is_plus
    end
    plus_candidates = expr.pairs[plus_candidates_idx]

    mul_vals = lhs.(mul_candidates)
    candidates = map(plus_candidates_idx, plus_candidates) do p_idx, p
        map(mul_candidates_idx, mul_vals) do m_idx, m_v
            if nameof(m_v) in nameof.(arguments(rhs(p)))
                (m_idx, m_v) => (p_idx, expr.pairs[p_idx])
            end
        end
    end
    candidates = filter(!isnothing, reduce(vcat, candidates))

    # @show plus_candidates

    pattern = map(plus_candidates_idx, plus_candidates) do plus_idx, c
        plus_args = arguments(rhs(c))
        mul_pattern = map(mul_candidates_idx, mul_candidates) do mul_idx, m
            mul_val = lhs(m)

            if nameof(mul_val) in nameof.(plus_args)
                A, B = arguments(rhs(m))
                Cs = filter(x -> nameof(x) != nameof(mul_val), plus_args)
                # @show validate_mul_shapes(A, B, Cs...)
                validate_mul_shapes(A, B, Cs...) || return nothing
                return (; A, B, Cs, mul_candidate = m, plus_candidate = c, mul_idx, plus_idx, pattern="A*B + C")
            end
        end
        # @show mul_pattern
        # only(filter(!isnothing, mul_pattern))
        filter(!isnothing, mul_pattern)
    end
    isempty(pattern) ? nothing : pattern
end

function detect_matmul_add_pattern(expr, state::CSEState)
    # Must be addition with exactly 2 arguments
    if !iscall(expr) || (operation(expr) !== +) || length(arguments(expr)) != 2
        return nothing
    end

    args = arguments(expr)

    if all(x -> x <: AbstractArray, symtype.(args))
        if (operation(expr) === +) && length(args) == 2
            cse_exprs = map(x -> find_cse_expr(x, state), args)
            C_idx = only(findfirst(isnothing, cse_exprs))
            var_idx = only(findfirst(!isnothing, cse_exprs))
            C = args[C_idx]
            var_ex = cse_exprs[var_idx].expr
            var_args = arguments(var_ex)
            @assert operation(var_ex) === *

            return (; A = var_args[1], B = var_args[2], C = C, original_expr = expr)
        end
    end
    return nothing
end

function transform_to_mul5_assignment(expr, match_data_, state::CSEState)
    # @show expr

    # Create temporary variable for the result
    # temp_var_sym = gensym("mul5_temp")
    # temp_var = Sym{T}(temp_var_sym; type=symtype(C))
    # T = vartype(C)

    m = map(match_data_) do match_data

        A, B = match_data.A, match_data.B
        Cs = match_data.Cs
        C, other_Cs... = Cs
        T = vartype(C)

        # Create temporary variable for the result
        temp_var_sym = gensym("mul5_temp")
        temp_var = Sym{T}(temp_var_sym; type=symtype(C))

        copy_call = Term{T}(copy, [C]; type=symtype(C))
        mul_call = Term{T}(LinearAlgebra.mul!,
            [temp_var, A, B, Const{T}(1), Const{T}(1)];
            type=symtype(C))

        # Add assignments to CSE state
        copy_assignment = Assignment(temp_var, copy_call)
        mul_assignment = Assignment(temp_var, mul_call)  # This overwrites temp_var with mul! result
        if !isempty(other_Cs)
            plus_call = Term{T}(+, [temp_var, other_Cs...]; type=symtype(C))
            final_assignment = Assignment(temp_var, plus_call)
        else
            final_assignment = Assignment(temp_var, temp_var)
        end
        [copy_assignment, mul_assignment, final_assignment]
    end |> Base.Fix1(reduce, vcat)

    push!(state.sorted_exprs, m...)
    temp_var = last(m).lhs
    Let(m, temp_var, false)
end

const MATMUL_ADD_RULE = OptimizationRule(
    "MatMul+Add",
    detect_matmul_add_pattern,
    transform_to_mul5_assignment,
    10
)

Base.isempty(l::Let) = isempty(l.pairs)   

# Apply optimization rules during CSE
function apply_optimization_rules(expr, state::CSEState, rules=[MATMUL_ADD_RULE])
    for rule in sort(rules, by=r->r.priority, rev=true)
        match_data = reduce(vcat, rule.detector(expr, state))
        if match_data !== nothing # || !isempty(match_data)
            # @show typeof(match_data)
            # @show rule.transformer(expr, first(match_data), state)
            return rule.transformer(expr, match_data, state)
            # return map(m -> walk_ir(rule.transformer(expr, m, state), Mul5Visitor()), match_data) |> first
            # return map(m -> walk_ir(rule.transformer(expr, m, state), Mul5Visitor()), match_data)
        end
    end
    return nothing
end