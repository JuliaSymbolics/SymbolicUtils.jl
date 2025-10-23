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

function is_cse_var(x)
    startswith(string(nameof(x)), "##cse")
end

function validate_mul_shapes(A, B, C)
    [shape(A)[1], shape(B)[2]] == shape(C)
end

function validate_mul_shapes(A, B, C...)
    return true
    [shape(A)[1], shape(B)[2]] == shape(first(C))
end

function detect_matmul_add_pattern(expr::Code.Let, state::Code.CSEState)
    mul_candidates_idx = findall(expr.pairs) do x
        iscall(rhs(x)) || return false
        args = arguments(rhs(x))
        all_arrays = all(y -> y <: AbstractArray, symtype.(args))
        is_mul = operation(rhs(x)) === *
        all_arrays && is_mul
    end
    mul_candidates = expr.pairs[mul_candidates_idx]

    plus_candidates_idx = findall(expr.pairs) do x
        iscall(rhs(x)) || return false
        args = arguments(rhs(x))
        all_arrays = all(y -> y <: AbstractArray, symtype.(args))
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

    pattern = map(plus_candidates_idx, plus_candidates) do plus_idx, c
        plus_args = arguments(rhs(c))
        mul_pattern = map(mul_candidates_idx, mul_candidates) do mul_idx, m
            mul_val = lhs(m)

            if nameof(mul_val) in nameof.(plus_args)
                A, B = arguments(rhs(m))
                Cs = filter(x -> nameof(x) != nameof(mul_val), plus_args)
                validate_mul_shapes(A, B, Cs...) || return nothing
                return (; A, B, Cs, mul_candidate = m, plus_candidate = c, mul_idx, plus_idx, pattern="A*B + C")
            end
        end
        filter(!isnothing, mul_pattern)
    end
    isempty(pattern) ? nothing : pattern
end

function transform_to_mul5_assignment(expr, match_data_, state::Code.CSEState)
    Cset = Set(filter(!is_cse_var, reduce(vcat,getproperty.(match_data_, :Cs))))
    final_temps = []

    m = map(match_data_) do match_data

        A, B = match_data.A, match_data.B
        C = pop!(Cset)
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
        final_assignment = Assignment(temp_var, temp_var)
        push!(final_temps, temp_var)

        [copy_assignment, mul_assignment, final_assignment]
    end |> Base.Fix1(reduce, vcat)

    push!(state.sorted_exprs, m...)
    temp_var = last(m).lhs
    Code.Let(m, +(final_temps..., Cset...), false)
end

const MATMUL_ADD_RULE = OptimizationRule(
    "MatMul+Add",
    detect_matmul_add_pattern,
    transform_to_mul5_assignment,
    10
)

Base.isempty(l::Code.Let) = isempty(l.pairs)   

# Apply optimization rules during CSE
function apply_optimization_rules(expr, state::Code.CSEState, rules=[MATMUL_ADD_RULE])
    for rule in sort(rules, by=r->r.priority, rev=true)
        match_data = reduce(vcat, rule.detector(expr, state))
        if match_data !== nothing # || !isempty(match_data)
            return rule.transformer(expr, match_data, state)
        end
    end
    return nothing
end