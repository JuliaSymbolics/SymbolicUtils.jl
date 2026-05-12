"""
Post-processing pass that splits large generated function bodies into smaller
"gadget" functions to reduce compile time.

The key insight: Julia's compiler has superlinear cost in function size.
Splitting a 3000-line function into smaller functions compiles much faster.

This pass targets `batched_setindex!` patterns writing to arrays (e.g., mass
matrices and RHS vectors). It clusters the computed values by shared
dependencies and extracts each cluster into a separate local function.

The gadget functions are closures defined inside the main body, so they can
capture variables like `__mtk_arg_2`, `t`, etc. from the enclosing scope.
Free CSE nodes (simple array accesses) are duplicated in each gadget body.
"""

const GADGET_MIN_ASSIGNMENTS = 200  # only split if body has this many CSE assignments
const GADGET_SHARED_THRESHOLD = 10  # nodes used by >= this many entries are "base"
const GADGET_OVERLAP_THRESHOLD = 0.3
const GADGET_BATCH_SIZE = 32

# ============================================================
# Symbol classification
# ============================================================

is_cse_symbol(s::Symbol) = startswith(String(s), "##cse#")
is_cse_symbol(_) = false

function cse_id(s::Symbol)
    str = String(s)
    return parse(Int, str[7:end])
end

# ============================================================
# Dependency finders (recursive Expr walkers)
# ============================================================

function find_cse_refs(expr)
    refs = Set{Symbol}()
    _find_cse_refs!(refs, expr)
    return refs
end

function _find_cse_refs!(refs::Set{Symbol}, expr::Expr)
    for arg in expr.args
        _find_cse_refs!(refs, arg)
    end
end

function _find_cse_refs!(refs::Set{Symbol}, s::Symbol)
    is_cse_symbol(s) && push!(refs, s)
end

_find_cse_refs!(::Set{Symbol}, _) = nothing

function find_misc_refs(expr)
    refs = Set{Symbol}()
    _find_misc_refs!(refs, expr)
    return refs
end

function _find_misc_refs!(refs::Set{Symbol}, expr::Expr)
    for arg in expr.args
        _find_misc_refs!(refs, arg)
    end
end

function _find_misc_refs!(refs::Set{Symbol}, s::Symbol)
    startswith(String(s), "__miscₛᵧₘ") && push!(refs, s)
end

_find_misc_refs!(::Set{Symbol}, _) = nothing

function find_free_refs(expr)
    refs = Set{Symbol}()
    _find_free_refs!(refs, expr)
    return refs
end

function _find_free_refs!(refs::Set{Symbol}, expr::Expr)
    for arg in expr.args
        _find_free_refs!(refs, arg)
    end
end

function _find_free_refs!(refs::Set{Symbol}, s::Symbol)
    str = String(s)
    (startswith(str, "__mtk_arg_") || s === :t) && push!(refs, s)
end

_find_free_refs!(::Set{Symbol}, _) = nothing

# ============================================================
# batched_setindex! parsing
# ============================================================

"""
    parse_batched_setindex_tuples(stmt)

If `stmt` is `_ = batched_setindex!(target, (vals...), (idxs...))` (optionally
wrapped in @inbounds), return `(target, vals_tuple, idxs_tuple)`. Otherwise `nothing`.
Constant fills (scalar value + array indices) are skipped.
"""
function parse_batched_setindex_tuples(stmt)
    Meta.isexpr(stmt, :(=)) || return nothing
    rhs = stmt.args[2]
    # Unwrap @inbounds macrocall if present
    if Meta.isexpr(rhs, :macrocall)
        inner = _find_inner_call(rhs)
        inner !== nothing && (rhs = inner)
    end
    Meta.isexpr(rhs, :call) || return nothing
    length(rhs.args) >= 4 || return nothing
    rhs.args[1] === batched_setindex! || return nothing
    vals = rhs.args[3]
    idxs = rhs.args[4]
    # Only match tuple values + tuple indices (skip constant fills)
    (Meta.isexpr(vals, :tuple) && Meta.isexpr(idxs, :tuple)) || return nothing
    return (rhs.args[2], vals, idxs)
end

function _find_inner_call(macrocall::Expr)
    for arg in macrocall.args
        if arg isa Expr && Meta.isexpr(arg, :call)
            return arg
        end
    end
    return nothing
end

"""
    parse_cartesian_index(expr) -> Tuple or nothing

`CartesianIndex(N)` -> `(N,)`, `CartesianIndex(N, M)` -> `(N, M)`.
"""
function parse_cartesian_index(expr)
    Meta.isexpr(expr, :call) || return nothing
    expr.args[1] === CartesianIndex || return nothing
    return Tuple(expr.args[2:end])
end

# ============================================================
# Main entry point
# ============================================================

"""
    split_into_gadgets!(body::Expr) -> Bool

Analyze a generated code block and split large `batched_setindex!` computation
clusters into separate gadget functions. Modifies `body` in place.

Expects `body` to be a flat `Expr(:block, stmts...)`.
"""
function split_into_gadgets!(body::Expr)
    # ----------------------------------------------------------
    # 1. Parse all CSE assignments
    # ----------------------------------------------------------
    AssignInfo = @NamedTuple{
        idx::Int, rhs::Any,
        cse_deps::Set{Symbol}, misc_deps::Set{Symbol}, free_deps::Set{Symbol}
    }
    assignments = Dict{Symbol, AssignInfo}()

    n_cse = 0
    for (i, stmt) in enumerate(body.args)
        Meta.isexpr(stmt, :(=)) || continue
        lhs, rhs = stmt.args[1], stmt.args[2]
        if is_cse_symbol(lhs)
            n_cse += 1
            rhs_e = rhs isa Expr ? rhs : Expr(:block, rhs)
            cd = find_cse_refs(rhs_e); delete!(cd, lhs)
            md = find_misc_refs(rhs_e)
            fd = find_free_refs(rhs_e)
            assignments[lhs] = (idx=i, rhs=rhs, cse_deps=cd, misc_deps=md, free_deps=fd)
        end
    end

    n_cse < GADGET_MIN_ASSIGNMENTS && return false

    # ----------------------------------------------------------
    # 2. Find batched_setindex! entries grouped by target
    # ----------------------------------------------------------
    target_entries = Dict{Any, Vector{Tuple{Symbol,Tuple}}}()
    target_stmt_indices = Dict{Any, Vector{Int}}()

    for (i, stmt) in enumerate(body.args)
        parsed = parse_batched_setindex_tuples(stmt)
        parsed === nothing && continue
        target, vals, idxs = parsed

        entries = get!(Vector{Tuple{Symbol,Tuple}}, target_entries, target)
        indices = get!(Vector{Int}, target_stmt_indices, target)
        push!(indices, i)

        for (val, idx_expr) in zip(vals.args, idxs.args)
            (val === 0 || val === 0.0 || !is_cse_symbol(val)) && continue
            idx = parse_cartesian_index(idx_expr)
            idx === nothing && continue
            push!(entries, (val, idx))
        end
    end

    total_entries = sum(length(es) for (_, es) in target_entries; init=0)
    total_entries < 10 && return false

    # ----------------------------------------------------------
    # 3. Compute "computed" dependency cones
    # ----------------------------------------------------------
    # A node is "computed" if it has CSE deps or misc deps (not just a free
    # array access like `__mtk_arg_2[N]`).
    dep_cache = Dict{Symbol, Set{Symbol}}()

    function computed_deps(sym::Symbol)
        haskey(dep_cache, sym) && return dep_cache[sym]
        result = Set{Symbol}()
        if haskey(assignments, sym)
            info = assignments[sym]
            if !isempty(info.cse_deps) || !isempty(info.misc_deps)
                push!(result, sym)
            end
            for dep in info.cse_deps
                union!(result, computed_deps(dep))
            end
        end
        dep_cache[sym] = result
        return result
    end

    all_entry_deps = Dict{Tuple{Symbol,Tuple}, Set{Symbol}}()
    node_usage = Dict{Symbol, Int}()

    for (_, entries) in target_entries
        for (val_sym, idx) in entries
            deps = computed_deps(val_sym)
            all_entry_deps[(val_sym, idx)] = deps
            for d in deps
                node_usage[d] = get(node_usage, d, 0) + 1
            end
        end
    end

    # ----------------------------------------------------------
    # 4. Identify base nodes and cluster per target
    # ----------------------------------------------------------
    base_nodes = Set{Symbol}(k for (k, v) in node_usage if v >= GADGET_SHARED_THRESHOLD)

    function cluster_target_entries(entries::Vector{Tuple{Symbol,Tuple}})
        isempty(entries) && return Vector{Vector{Tuple{Symbol,Tuple}}}()
        private = Dict(e => setdiff(all_entry_deps[e], base_nodes) for e in entries)

        # Union-Find
        N = length(entries)
        parent = collect(1:N)
        function uf_find(x)
            while parent[x] != x
                parent[x] = parent[parent[x]]
                x = parent[x]
            end
            return x
        end

        n2e = Dict{Symbol, Vector{Int}}()
        for (i, e) in enumerate(entries)
            for n in private[e]
                push!(get!(Vector{Int}, n2e, n), i)
            end
        end

        for (_, eidxs) in n2e
            for j in 2:length(eidxs)
                i1, i2 = eidxs[1], eidxs[j]
                p1, p2 = private[entries[i1]], private[entries[i2]]
                (isempty(p1) || isempty(p2)) && continue
                ol = length(intersect(p1, p2))
                ms = min(length(p1), length(p2))
                if ms > 0 && ol / ms > GADGET_OVERLAP_THRESHOLD
                    r1, r2 = uf_find(i1), uf_find(i2)
                    r1 != r2 && (parent[r1] = r2)
                end
            end
        end

        clusters = Dict{Int, Vector{Tuple{Symbol,Tuple}}}()
        for (i, e) in enumerate(entries)
            push!(get!(Vector{Tuple{Symbol,Tuple}}, clusters, uf_find(i)), e)
        end
        return sort!(collect(values(clusters)), by=c -> -length(c))
    end

    # ----------------------------------------------------------
    # 5. Compute transitive deps for gadget bodies
    # ----------------------------------------------------------
    function all_transitive(sym::Symbol, stop_set::Set{Symbol},
                            cache::Dict{Symbol, Set{Symbol}})
        haskey(cache, sym) && return cache[sym]
        result = Set{Symbol}()
        if sym in stop_set || !haskey(assignments, sym)
            cache[sym] = result
            return result
        end
        push!(result, sym)
        for dep in assignments[sym].cse_deps
            union!(result, all_transitive(dep, stop_set, cache))
        end
        cache[sym] = result
        return result
    end

    # -- Base gadget --
    base_cache = Dict{Symbol, Set{Symbol}}()
    empty_stop = Set{Symbol}()
    base_all = Set{Symbol}()
    for bn in base_nodes
        union!(base_all, all_transitive(bn, empty_stop, base_cache))
    end
    filter!(n -> haskey(assignments, n), base_all)

    base_misc = Set{Symbol}()
    for n in base_all
        union!(base_misc, assignments[n].misc_deps)
    end
    base_body = sort!(collect(base_all), by=n -> assignments[n].idx)
    base_outputs = sort!(collect(base_nodes), by=cse_id)

    # -- Cluster gadgets per target --
    all_gadget_nodes = copy(base_all)
    target_order = sort!(collect(keys(target_entries)), by=repr)
    cluster_cache = Dict{Symbol, Set{Symbol}}()  # shared across targets (same stop_set)

    # Gadget descriptor type
    GadgetInfo = @NamedTuple{
        name::Symbol,
        body_syms::Vector{Symbol},
        output_syms::Vector{Symbol},
        base_inputs::Vector{Symbol},
        misc_inputs::Vector{Symbol},
        target::Any,
        sorted_entries::Vector{Tuple{Symbol,Tuple}},
    }
    gadgets = GadgetInfo[]

    if !isempty(base_nodes)
        push!(gadgets, (
            name = :_gadget_base!,
            body_syms = base_body,
            output_syms = base_outputs,
            base_inputs = Symbol[],
            misc_inputs = sort!(collect(base_misc)),
            target = nothing,
            sorted_entries = Tuple{Symbol,Tuple}[],
        ))
    end

    for (ti, target) in enumerate(target_order)
        clusters = cluster_target_entries(target_entries[target])

        for (ci, cluster) in enumerate(clusters)
            cluster_private = Set{Symbol}()
            for e in cluster
                union!(cluster_private, setdiff(all_entry_deps[e], base_nodes))
            end

            cluster_all = Set{Symbol}()
            for pn in cluster_private
                union!(cluster_all, all_transitive(pn, base_nodes, cluster_cache))
            end
            filter!(n -> haskey(assignments, n), cluster_all)

            c_base = Set{Symbol}()
            c_misc = Set{Symbol}()
            for n in cluster_all
                union!(c_misc, assignments[n].misc_deps)
                for dep in assignments[n].cse_deps
                    dep in base_nodes && push!(c_base, dep)
                end
            end

            c_body = sort!(collect(cluster_all), by=n -> assignments[n].idx)
            sorted_ents = sort(cluster, by=x -> x[2])
            c_outputs = Symbol[v for (v, _) in sorted_ents]

            push!(gadgets, (
                name = Symbol("_gadget_t$(ti)_c$(ci)!"),
                body_syms = c_body,
                output_syms = c_outputs,
                base_inputs = sort!(collect(c_base), by=cse_id),
                misc_inputs = sort!(collect(c_misc)),
                target = target,
                sorted_entries = sorted_ents,
            ))

            union!(all_gadget_nodes, cluster_all)
        end
    end

    # Need at least one cluster gadget to justify splitting
    n_clusters = count(g -> g.name !== :_gadget_base!, gadgets)
    n_clusters < 1 && return false

    # ----------------------------------------------------------
    # 6. Determine which statements to remove from main body
    # ----------------------------------------------------------
    remove_indices = Set{Int}()

    # Remove "computed" gadget nodes (those with non-trivial deps).
    # Free nodes (array accesses with no CSE/misc deps) are kept in
    # the main body AND duplicated in gadget bodies — they're cheap.
    for sym in all_gadget_nodes
        haskey(assignments, sym) || continue
        info = assignments[sym]
        if !isempty(info.cse_deps) || !isempty(info.misc_deps)
            push!(remove_indices, info.idx)
        end
    end

    # Remove old batched_setindex! statements (we re-emit them)
    for (_, indices) in target_stmt_indices
        union!(remove_indices, indices)
    end

    # ----------------------------------------------------------
    # 7. Build new body statements
    # ----------------------------------------------------------
    new_stmts = Any[]

    # 7a. Function definitions (closures capturing enclosing scope)
    for g in gadgets
        fn_params = Symbol[g.base_inputs; g.misc_inputs]

        fn_body = Expr(:block)
        for sym in g.body_syms
            push!(fn_body.args, Expr(:(=), sym, assignments[sym].rhs))
        end
        if length(g.output_syms) == 1
            push!(fn_body.args, Expr(:return, g.output_syms[1]))
        else
            push!(fn_body.args, Expr(:return, Expr(:tuple, g.output_syms...)))
        end

        wrapped = Expr(:macrocall, Symbol("@inbounds"), LineNumberNode(0), fn_body)
        fn_def = Expr(:function, Expr(:call, g.name, fn_params...), wrapped)
        push!(new_stmts, fn_def)
    end

    # 7b. Keep non-removed original statements (structural code, misc assigns, etc.)
    for (i, stmt) in enumerate(body.args)
        i ∉ remove_indices && push!(new_stmts, stmt)
    end

    # 7c. Base gadget call
    for g in gadgets
        g.name === :_gadget_base! || continue
        call_args = Any[g.base_inputs; g.misc_inputs]
        if length(g.output_syms) == 1
            push!(new_stmts, Expr(:(=), g.output_syms[1],
                                  Expr(:call, g.name, call_args...)))
        else
            push!(new_stmts, Expr(:(=), Expr(:tuple, g.output_syms...),
                                  Expr(:call, g.name, call_args...)))
        end
    end

    # 7d. Cluster gadget calls + batched writes, grouped by target
    for target in target_order
        # Cluster calls
        all_batch = Tuple{Symbol, Tuple}[]

        for g in gadgets
            g.target === target || continue
            call_args = Any[g.base_inputs; g.misc_inputs]

            prefix = String(g.name)[1:end-1]  # strip trailing !
            output_locals = [Symbol("$(prefix)_v$(j)") for j in eachindex(g.output_syms)]

            if length(output_locals) == 1
                push!(new_stmts, Expr(:(=), output_locals[1],
                                      Expr(:call, g.name, call_args...)))
            else
                push!(new_stmts, Expr(:(=), Expr(:tuple, output_locals...),
                                      Expr(:call, g.name, call_args...)))
            end

            # Collect batch write entries (output_local -> CartesianIndex)
            for (j, (_, idx)) in enumerate(g.sorted_entries)
                push!(all_batch, (output_locals[j], idx))
            end
        end

        # Batched writes
        for bs in 1:GADGET_BATCH_SIZE:length(all_batch)
            be = min(bs + GADGET_BATCH_SIZE - 1, length(all_batch))
            batch = @view all_batch[bs:be]
            vals_expr = Expr(:tuple, (name for (name, _) in batch)...)
            idxs_expr = Expr(:tuple, (Expr(:call, CartesianIndex, idx...)
                                      for (_, idx) in batch)...)
            push!(new_stmts, Expr(:(=), :_,
                                  Expr(:call, batched_setindex!, target, vals_expr, idxs_expr)))
        end
    end

    # Replace body contents
    empty!(body.args)
    append!(body.args, new_stmts)

    return true
end
