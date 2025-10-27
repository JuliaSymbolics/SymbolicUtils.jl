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

                @show validate_mul_shapes(A, B, Cs...)
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

    m_ = map(match_data_) do match_data

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
    end
    m = m_ |> Base.Fix1(reduce, vcat)

    transformed_idxs = getproperty.(match_data_, :plus_idx)
    substitution_map = get_substitution_map(match_data_, m_)
    rm_idxs = getproperty.(match_data_, :mul_idx)
    transformations = Dict()
    map(transformed_idxs, m_) do i, mm
        bank(transformations, i, mm)
    end

    new_pairs = []
    for (i, e) in enumerate(expr.pairs)
        if i in transformed_idxs
            push!(new_pairs, transformations[i]...)
            @show e
        elseif i in rm_idxs
            push!(new_pairs, nothing)
        else
            push!(new_pairs, e)
        end
    end
    new_pairs = filter(!isnothing, new_pairs)

    push!(state.sorted_exprs, m...)
    temp_var = last(m).lhs
    new_let = Code.Let(new_pairs, expr.body, expr.let_block)
    apply_substitution_map(new_let, substitution_map)
end

function get_substitution_map(match_data, transformations)
    dic = Dict()
    @assert length(match_data) == length(transformations)

    plus_idxs = getproperty.(match_data, :plus_idx)

    map(match_data, transformations) do m, t
        bank(dic, m.plus_candidate.lhs, t[end].lhs)
    end
    dic
end

function bank(dic, key, value)
    if haskey(dic, key)
        dic[key] = vcat(dic[key], value)
    else
        dic[key] = value
    end
end

function apply_substitution_map(expr::Code.Let, substitution_map::Dict)
    substitute_in_ir(expr, substitution_map)
end

function substitute_in_ir(s::Symbol, substitution_map::Dict)
    get(substitution_map, s, s)
end

function substitute_in_ir_base(s, substitution_map::Dict)
    @warn s, substitution_map
    get(substitution_map, s, s)
end

function substitute_in_ir(expr, substitution_map::Dict)
    if iscall(expr)
        new_args = map(arguments(expr)) do arg
            substitute_in_ir(arg, substitution_map)
        end
        return Code.Term{Code.vartype(expr)}(operation(expr), new_args; type=Code.symtype(expr))
    elseif issym(expr)
        substitute_in_ir_base(expr, substitution_map)
    else
        expr
    end
end

function substitute_in_ir(x::Code.Assignment, substitution_map::Dict)
    new_lhs = substitute_in_ir(Code.lhs(x), substitution_map)
    new_rhs = substitute_in_ir(Code.rhs(x), substitution_map)
    return Code.Assignment(new_lhs, new_rhs)
end

function substitute_in_ir(expr::Code.Let, substitution_map::Dict)
    isempty(substitution_map) && return expr

    new_pairs = map(expr.pairs) do p
        substitute_in_ir(p, substitution_map)
    end
    new_body = substitute_in_ir(expr.body, substitution_map)
    return Code.Let(new_pairs, new_body, expr.let_block)
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