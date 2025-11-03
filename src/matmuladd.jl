# Pattern-based optimization templates for CSE

"""
    OptimizationRule(name, detector, transformer, priority)

Defines an optimization rule with:
- `name`: A string identifier for the optimization.
- `detector`: A function that detects patterns in the IR. 
- `transformer`: A function that transforms the IR based on detected patterns, and returns updated IR
- `priority`: Integer priority (higher = applied first)

The detector function should implement the signature

```julia
detector(expr::Code.Let, state::Code.CSEState) -> Union{Nothing, Vector{<:AbstractMatched}}
```

Likewise, the transformer function should implement the signature

```julia
transformer(expr::Code.Let, match_data::Union{Nothing, Vector{<:AbstractMatched}}, state::Code.CSEState) -> Code.Let
```
"""
struct OptimizationRule{N, D, T, P}
    name::N
    detector::D
    transformer::T
    priority::P
end

abstract type AbstractMatched end

struct MatMulAddMatch{At, Bt, Ct} <: AbstractMatched
    A::At
    B::Bt
    Cs::Ct
    mul_candidate::Code.Assignment
    plus_candidate::Code.Assignment
    mul_idx::Int
    plus_idx::Int
    pattern::String
end

"""
    detect_matmul_add_pattern(expr::Code.Let, state::Code.CSEState) -> Union{Nothing, Vector{MatMulAddMatch}}

Attempts to detect patterns of the form:

```julia
result = A * B + C
```

And replaces them with in-place multiplication and addition:

```julia
copy!(temp, C)
mul!(temp, A, B, 1, 1)
result = temp
```

`A` and `B` must not be aliased.
"""
function detect_matmul_add_pattern(expr::Code.Let, state::Code.CSEState)
    mul_candidates_idx = findall(expr.pairs) do x
        r = rhs(x)
        iscall(r) || return false
        all_arrays = symtype(r) <: AbstractArray
        is_mul = operation(r) === *
        all_arrays && is_mul
    end
    mul_candidates = expr.pairs[mul_candidates_idx]

    plus_candidates_idx = findall(expr.pairs) do x
        r = rhs(x)
        iscall(r) || return false
        all_arrays = symtype(r) <: AbstractArray
        is_plus = isadd(r)
        all_arrays && is_plus
    end
    plus_candidates = expr.pairs[plus_candidates_idx]

    candidates = map(plus_candidates_idx, plus_candidates) do p_idx, p

        map(mul_candidates_idx, mul_candidates) do m_idx, m_v
            if nameof(lhs(m_v)) in nameof.(arguments(rhs(p)))
                (m_idx, m_v) => (p_idx, expr.pairs[p_idx])
            end
        end
    end
    candidates = filter(!isnothing, reduce(vcat, candidates))

    all_additive_terms = map(candidates) do c
        arguments(rhs(c[2][2]))
    end |> Iterators.flatten |> Set
    all_multiplicative_terms = Set(lhs.(mul_candidates))
    net_additive_terms = setdiff(all_additive_terms, all_multiplicative_terms)

    matches = MatMulAddMatch[]

    for ((mul_idx, mul_val), (plus_idx, plus_val)) in candidates
        A, B... = arguments(rhs(expr.pairs[mul_idx]))
        Cs = isempty(net_additive_terms) ? continue : [pop!(net_additive_terms)]
        push!(matches, MatMulAddMatch(A, B, Cs, expr.pairs[mul_idx], plus_val, mul_idx, plus_idx, "A*B + C"))
    end

    isempty(matches) ? nothing : matches, net_additive_terms
end

transform_to_mul5_assignment(expr, ::Union{Nothing, AbstractVector{Nothing}, Tuple{Nothing, Nothing}}, state::Code.CSEState) = expr
function transform_to_mul5_assignment(expr, match_data_, state::Code.CSEState)
    match_data_, net_additive_terms = match_data_
    Cset = Set(Iterators.flatten(getproperty.(match_data_, :Cs)))

    m_ = map(match_data_) do match_data

        A, B = match_data.A, match_data.B
        C = pop!(Cset)
        T = vartype(C)

        # Create temporary variable for the result
        temp_var_sym = gensym("mul5_temp")
        temp_var = Sym{T}(temp_var_sym; type=symtype(C))

        if B isa AbstractVector{<:BasicSymbolic}
            if length(B) == 1
                B = B[1]
            else
                B = Term{T}(*, B, type=symtype(C))
            end
        end

        copy_call = Term{T}(copy, [C]; type=symtype(C))
        mul_call = Term{T}(LinearAlgebra.mul!,
            [temp_var, A, B, Const{T}(1), Const{T}(1)];
            type=symtype(C))

        # Add assignments to CSE state
        copy_assignment = Assignment(temp_var, copy_call)
        mul_assignment = Assignment(temp_var, mul_call)  # This overwrites temp_var with mul! result
        final_assignment = Assignment(temp_var, temp_var)

        [copy_assignment, mul_assignment, final_assignment]
    end

    transformed_idxs = getproperty.(match_data_, :plus_idx)
    substitution_map = get_substitution_map(match_data_, m_)
    rm_idxs = getproperty.(match_data_, :mul_idx)
    transformations = Dict()
    for (i, mm) in zip(transformed_idxs, m_)
        bank(transformations, i, mm)
    end

    new_pairs = []
    for (i, e) in enumerate(expr.pairs)
        if i in transformed_idxs
            append!(new_pairs, transformations[i])
        elseif i in rm_idxs
            # do nothing/ skip over
            # TODO: handle expr9 when a hanging mul is filtered out
        else
            push!(new_pairs, e)
        end
    end

    bank(substitution_map, last(match_data_).plus_candidate.lhs, collect(Cset))
    bank(substitution_map, last(match_data_).plus_candidate.lhs, collect(net_additive_terms))

    new_let = Code.Let(new_pairs, expr.body, expr.let_block)
    transformed_ir = apply_substitution_map(new_let, substitution_map)

    transformed_ir
end

function get_substitution_map(match_data, transformations)
    dic = Dict()
    @assert length(match_data) == length(transformations)

    for (m, t) in zip(match_data, transformations)
        bank(dic, m.plus_candidate.lhs, t[2].lhs)
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
    if haskey(substitution_map, s)
        v = substitution_map[s]
        if issym(v)
            v
        else
            add_worker(vartype(first(v)), v)
        end
    else
        s
    end
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

"""
    substitute_in_ir(expr::Code.Let, substitution_map::Dict) -> Code.Let

Recursively substitutes variables in the IR `expr` according to `substitution_map`.
"""
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
function apply_optimization_rules(expr, state::Code.CSEState, rules)
    match_data = rules.detector(expr, state)
    if match_data !== nothing
        return rules.transformer(expr, match_data, state)
    end

    return nothing
end