# WARN: `IRStructure` should NOT subtype `AbstractArray`, or this will cause
# invalidations/ambiguities due to symbolic array `getindex`.

"""
    $TYPEDEF

Linear IR representation of a (collection of) symbolic expressions. This can be used to
accelerate operations such as `search_variables!` if frequently performed on the same/similar
expressions.

# Invariants

The `dependency_graph` correctly encodes the argument structure of every expression in the
IR. For expression at index `i`, `Graphs.outneighbors(dependency_graph, i)` yields
dependency indices in the following order: the index of `operation(ir[i])` first (if it is
a `BasicSymbolic`), then the indices of `arguments(ir[i])` in order.

## Extended help

The following details are internal

### Fields

$TYPEDFIELDS
"""
struct IRStructure{T}
    """
    Dependency graph (DAG), where `Graphs.outneighbors(g, v)` denotes the nodes that the
    expression at index `v` depends on. Out-neighbors are in argument order: the operation
    (if symbolic) comes first, followed by `arguments` in order.
    """
    dependency_graph::OrderedDiGraph
    """
    Mapping from linear indices to the expression at that index.
    """
    symbols::Vector{BasicSymbolic{T}}
    """
    Inverse mapping of `symbols`.
    """
    definition::IdDict{BasicSymbolic{T}, Int}
    """
    A cached `BitVector` to be used for several operations supported by this struct. It
    is required for many common operations, and `fill!(false, cached_mask)` is much faster
    than allocating a new one of the appropriate size.
    """
    cached_mask::BitVector
    """
    Similar to `cached_mask` but a `Vector{Int}`.
    """
    cached_idxs::Vector{Int}
end

"""
    $TYPEDSIGNATURES

Create an empty `IRStructure` to store `BasicSymbolic{T}` expressions.
"""
function IRStructure{T}() where {T}
    ir = IRStructure{T}(
        OrderedDiGraph(), BasicSymbolic{T}[],
        IdDict{BasicSymbolic{T}, Int}(), BitVector(), Int[]
    )
    # It's pretty easy to hit this
    sizehint!(ir, 100)
    return ir
end

"""
    $TYPEDSIGNATURES

Get the cached `BitVector` inside IR, after filling it with `false`.
"""
function get_cached_mask!(ir::IRStructure)
    mask = ir.cached_mask
    fill!(mask, false)
    return mask
end

"""
    $TYPEDSIGNATURES

Get the cached `BitVector` inside IR, after resizing it to have a length of at least `n` and
filling it with `false`.
"""
function get_cached_mask!(ir::IRStructure, n::Integer)
    mask = ir.cached_mask
    length(mask) < n && resize!(mask, n)
    fill!(mask, false)
    return mask
end

"""
    $TYPEDSIGNATURES

Get the cached `Vector{Int}` inside IR.
"""
function get_cached_idxs!(ir::IRStructure)
    return ir.cached_idxs
end

function _get_reachability_dfs!(reachability::Vector{Int}, visited::BitVector, ir::IRStructure, cur::Int)
    visited[cur] = true
    for nbor in Graphs.outneighbors(ir.dependency_graph, cur)
        visited[nbor] && continue
        _get_reachability_dfs!(reachability, visited, ir, nbor)
    end
    push!(reachability, cur)
    return nothing
end

"""
    $TYPEDSIGNATURES

Compute the transitive closure of `dependency_graph` from node `idx` via DFS postorder,
returning a topologically sorted `Vector{Int}` of all node indices that `idx` (directly or
indirectly) depends on. Dependencies (children) appear before the expressions that depend on
them (parents). Writes the result to and returns `reachability`.

This function allocates its own scratch space and does not use `ir.cached_mask` or
`ir.cached_idxs`, so it is safe to call even when those are held by an outer caller.
"""
function get_reachability!(reachability::Vector{Int}, ir::IRStructure, idx::Int)
    g = ir.dependency_graph
    n = length(ir)
    visited = falses(n)
    sizehint!(reachability, n)
    visited[idx] = true
    for nbor in Graphs.outneighbors(g, idx)
        visited[nbor] && continue
        _get_reachability_dfs!(reachability, visited, ir, nbor)
    end
    return reachability
end

"""
    $TYPEDSIGNATURES

Out-of-place version of [`get_reachability!`](@ref).
"""
get_reachability(ir::IRStructure, idx::Int) = get_reachability!(Int[], ir, idx)

"""
    $TYPEDSIGNATURES

Preallocate space for `n` nodes in `ir`.
"""
function Base.sizehint!(ir::IRStructure, n::Integer)
    sizehint!(ir.symbols, n)
    sizehint!(ir.definition, n)
    sizehint!(ir.cached_mask, n)
    sizehint!(ir.cached_idxs, n)
    return ir
end

"""
    $TYPEDSIGNATURES

Number of nodes in `ir`.
"""
Base.length(ir::IRStructure) = length(ir.symbols)
"""
    $TYPEDSIGNATURES

Find the symbolic expression at index `i`.
"""
Base.getindex(ir::IRStructure, i::Integer) = ir.symbols[i]
"""
    $TYPEDSIGNATURES

Get the index that a symbolic expression occurs at in `ir`. Does not modify `ir`.
"""
Base.getindex(ir::IRStructure{T}, i::BasicSymbolic{T}) where {T} = ir.definition[i]
Base.IndexStyle(::Type{T}) where {T <: IRStructure} = IndexLinear()
"""
    $TYPEDSIGNATURES

Iterate over valid node indices in `ir`.
"""
Base.eachindex(ir::IRStructure) = eachindex(ir.symbols)

function _print_ssa_var(io::IO, i::Int)
    printstyled(io, "%", i; color = :yellow)
end

"""
    $TYPEDSIGNATURES

Print the IR representation of `ir` to `io`, showing at most `limit` statements.
If the IR has more statements than `limit`, the remaining statements are truncated
and a summary line is printed instead. Pass `limit = nothing` to print all statements.

See also [`SymbolicUtils.print_ir`](@ref) which defaults to printing all statements.
"""
function _show_ir(io::IO, ir::IRStructure; limit::Union{Int, Nothing} = 50)
    n = length(ir)
    println(io, "IRStructure with $n node$(n == 1 ? "" : "s"):")
    n == 0 && return

    g = ir.dependency_graph

    # A node is a "print leaf" if it will be emitted as a single unit by Julia's
    # symbolic printer rather than decomposed into op + SSA-ref arguments.
    # This covers:
    #   - default_is_atomic: plain Syms, Operator calls, dependent-variable calls
    #   - calls whose operation is any BasicSymbolic (e.g. x(t) from @syms x(t)),
    #     since those will be printed as "x(t)" directly regardless of whether x
    #     is a function symbolic or a dependent variable.
    is_print_leaf = default_is_atomic ∘ Base.Fix1(getindex, ir)

    # Compute topological order once: parents before children (since edges go
    # parent→dependency). Used to propagate visibility top-down and to print
    # dependencies before the nodes that reference them.
    topo = Graphs.topological_sort_by_dfs(g)

    # `to_expand[i]`: i is visible (reachable from a root without crossing print-leaves)
    # `indeg[i]`:     number of visible non-leaf ancestors that directly use i
    #
    # Expansion pass: iterate parents before children so that `to_expand` is
    # propagated correctly from roots downward.
    to_expand = falses(n)
    indeg = zeros(Int, n)
    for i in 1:n
        Graphs.indegree(g, i) == 0 && (to_expand[i] = true)
    end
    for i in topo
        to_expand[i] || continue
        is_print_leaf(i) && continue
        for j in Graphs.outneighbors(g, i)
            indeg[j] += 1
            to_expand[j] = true
        end
    end

    # Assign consecutive SSA indices to non-inlineable visible nodes
    # (indeg == 0 are roots; indeg > 1 are shared).
    # Iterate children before parents so dependencies receive lower SSA numbers.
    new_idx = zeros(Int, n)
    counter = 0
    for i in Iterators.reverse(topo)
        (to_expand[i] && indeg[i] != 1) || continue
        new_idx[i] = (counter += 1)
    end

    total_stmts = counter

    # Recursively print the expression at node `i`. Print-leaves are emitted
    # directly via Julia's symbolic printer so their internal structure is never
    # decomposed into SSA references. Single-use (inlineable) non-leaf nodes are
    # expanded in place; shared nodes are referenced by their SSA variable.
    function print_expr(i)
        sym = ir[i]
        if is_print_leaf(i) || !iscall(sym)
            print(io, sym)
            return
        end
        print(io, operation(sym))
        print(io, "(")
        for (j, arg) in enumerate(arguments(sym))
            j > 1 && print(io, ", ")
            arg_idx = ir.definition[arg]
            indeg[arg_idx] == 1 ? print_expr(arg_idx) : _print_ssa_var(io, new_idx[arg_idx])
        end
        print(io, ")")
    end

    # Print in children-before-parents order so that each SSA variable is defined
    # before it is referenced by a later statement.
    printed = 0
    for i in Iterators.reverse(topo)
        (to_expand[i] && indeg[i] != 1) || continue
        if limit !== nothing && printed >= limit
            remaining = total_stmts - printed
            print(io, "  ⋮ ($remaining more statement$(remaining == 1 ? "" : "s") omitted; use `print_ir` to show all)")
            println(io)
            return
        end
        print(io, "  ")
        _print_ssa_var(io, new_idx[i])
        print(io, " = ")
        print_expr(i)
        println(io)
        printed += 1
    end
end

function Base.show(io::IO, ir::IRStructure)
    _show_ir(io, ir; limit = 50)
end

"""
    print_ir([io::IO], ir::IRStructure)

Print the complete IR of `ir` to `io` (defaulting to `stdout`) without truncation.

By default, `show` limits the output to 50 statements. Use this function when
you need to inspect an `IRStructure` with more statements than that limit.
"""
print_ir(io::IO, ir::IRStructure) = _show_ir(io, ir; limit = nothing)
print_ir(ir::IRStructure) = print_ir(stdout, ir)

const IRBookmarkT = Int

"""
    $TYPEDSIGNATURES

Obtain a token representing the current state of `ir`. After populating `ir` with additional
expressions, it can be rolled back to the point of the bookmark using
[`SymbolicUtils.rollback!`](@ref). Note that deleting nodes present in `ir` when it was
bookmarked is undefined behavior, and will invalidate the bookmark. Attempting to rollback
to invalidated bookmarks is undefined behavior. In case multiple bookmarks are made,
rolling back to an earlier bookmark invalidates subsequent bookmarks.
"""
function bookmark(ir::IRStructure)::IRBookmarkT
    return length(ir)
end

"""
    $TYPEDSIGNATURES

Revert `ir` to the state it had when the bookmark `bm` was made. See
[`SymbolicUtils.bookmark`](@ref) for further details.
"""
function rollback!(ir::IRStructure, bm::IRBookmarkT)
    to_rm = length(ir):-1:(bm + 1)
    # `rem_vertices!` is pretty slow
    for vert in to_rm
        Graphs.rem_vertex!(ir.dependency_graph, vert)
        delete!(ir.definition, ir.symbols[vert])
    end
    resize!(ir.symbols, bm)
    return ir
end

"""
    $TYPEDEF

Closure used to make [`populate_ir!`](@ref) type-stable.
"""
struct PopulateClosure{T} <: Function
    """
    The IR begin populated.
    """
    ir::IRStructure{T}
    """
    The expression to add to the IR, if it doesn't already exist.
    """
    expr::BasicSymbolic{T}
end

function (pc::PopulateClosure{T})() where {T}
     (; ir, expr) = pc
     Graphs.add_vertex!(ir.dependency_graph)
     idx = Graphs.nv(ir.dependency_graph)
     push!(ir.symbols, expr)           # must happen before add_edge! calls below
                                       # so recursive populate_ir! sees correct nv
     if iscall(expr)
         op = operation(expr)
         if op isa BasicSymbolic{T}
             op_idx = populate_ir!(ir, op)
             Graphs.add_edge!(ir.dependency_graph, idx, op_idx)
         end
         args = parent(arguments(expr))
         @union_split_smallvec args for arg in args
             arg_idx = populate_ir!(ir, arg)
             Graphs.add_edge!(ir.dependency_graph, idx, arg_idx)
         end
     end
     return idx
 end

"""
    $TYPEDSIGNATURES

Add the expression `expr` to `ir`.
"""
function populate_ir!(ir::IRStructure{T}, expr::BasicSymbolic{T}) where {T}
    return get!(PopulateClosure(ir, expr), ir.definition, expr)
end

"""
    $TYPEDSIGNATURES

Add the each expression in `exprs` to `ir`, in order.
"""
function populate_ir!(ir::IRStructure{T}, exprs::AbstractArray{BasicSymbolic{T}}) where {T}
    map(Base.Fix1(populate_ir!, ir), exprs)
end

@noinline function _throw_expr_not_in_ir(expr)
    throw(ArgumentError(lazy"Expression $expr was not found in the IR!"))
end

"""
    $TYPEDSIGNATURES

Return a new [`SymbolicUtils.IRStructure`](@ref) containing only the expressions in `exprs`
along with their dependencies.
"""
function subset_ir(ir::IRStructure{T}, exprs::AbstractVector{BasicSymbolic{T}}) where {T}
    new_ir = IRStructure{T}()
    reachables = get_cached_mask!(ir, length(ir))
    expr_reach = get_cached_idxs!(ir)
    for expr in exprs
        expr_i = get(ir.definition, expr, 0)
        iszero(expr_i) && _throw_expr_not_in_ir(expr)
        reachables[expr_i] = true
        empty!(expr_reach)
        get_reachability!(expr_reach, ir, expr_i)
        reachables[expr_reach] .= true
    end

    n_new_verts = count(reachables)
    Graphs.add_vertices!(new_ir.dependency_graph, n_new_verts)
    sizehint!(new_ir, n_new_verts)

    # Instead of calling `populate_ir!`, we can directly build the new IR.
    # Iterate in topological order (children before parents) so that when we
    # translate edges to new indices, the dependency is already in `new_ir.definition`.
    topo_order = Graphs.topological_sort_by_dfs(ir.dependency_graph)
    inew = 0
    for iold in Iterators.reverse(topo_order)
        reachables[iold] || continue
        inew += 1
        # Add expression to the IR
        sym = ir.symbols[iold]
        push!(new_ir.symbols, sym)
        new_ir.definition[sym] = inew

        # Translate old neighbors to new ones. Since we're iterating
        # `reachables` in topologically sorted order, we can guarantee that these
        # have already been added to `new_ir`.
        oldnbors = Graphs.outneighbors(ir.dependency_graph, iold)
        for nbor in oldnbors
            nsym = ir.symbols[nbor]
            nbor_idx = new_ir.definition[nsym]
            Graphs.add_edge!(new_ir.dependency_graph, inew, nbor_idx)
        end
    end

    return new_ir
end

"""
    $TYPEDSIGNATURES

Optimized version of [`SymbolicUtils.search_variables!`](@ref) that leverages the provided
[`SymbolicUtils.IRStructure`](@ref). May also add `expr` to `ir` in the process.
"""
function search_variables!(
        buffer, ir::IRStructure{T}, expr::BasicSymbolic{T}; is_atomic::F = default_is_atomic,
        recurse::G = iscall
    ) where {T, F, G}
    if is_atomic(expr)
        push!(buffer, expr)
        return
    end
    recurse(expr) || return
    idx = populate_ir!(ir, expr)
    # We don't have a fast path here, since `is_atomic` also prevents recursing into
    # subtrees. Thus, we always have to use the general BFS approach.

    # This is basically equivalent to a BFS, since `recurse` may filter out sections of the
    # DAG which means we can't just iterate over the reachable vertices.
    mask = get_cached_mask!(ir, length(ir))
    for arg_i in Graphs.outneighbors(ir.dependency_graph, idx)
        mask[arg_i] = true
    end

    reachability = get_cached_idxs!(ir)
    empty!(reachability)
    get_reachability!(reachability, ir, idx)
    for cur_i in Iterators.reverse(reachability)
        mask[cur_i] || continue
        cur = ir[cur_i]
        if is_atomic(cur)
            push!(buffer, cur)
            continue
        end
        recurse(cur) || continue
        for arg_i in Graphs.outneighbors(ir.dependency_graph, cur_i)
            mask[arg_i] = true
        end
    end
    return nothing
end

"""
    $TYPEDSIGNATURES

Optimized version of [`SymbolicUtils.query`](@ref) that leverages the provided
[`SymbolicUtils.IRStructure`](@ref). Requires that `expr` is present in `ir`.
"""
function query(predicate::F, ir::IRStructure{T}, expr::BasicSymbolic{T}; recurse::G = iscall) where {F, T, G}
    predicate(expr) && return true
    idx = ir.definition[expr]
    reachability = get_cached_idxs!(ir)
    # Fast path when we know we don't have to filter out subtrees
    if recurse === iscall
        empty!(reachability)
        get_reachability!(reachability, ir, idx)
        for i in reachability
            predicate(ir.symbols[i]) && return true
        end

        return false
    end

    # Similar to BFS in `search_variables!`
    mask = get_cached_mask!(ir, length(ir))
    for arg_i in Graphs.outneighbors(ir.dependency_graph, idx)
        mask[arg_i] = true
    end

    empty!(reachability)
    get_reachability!(reachability, ir, idx)
    for cur_i in Iterators.reverse(reachability)
        mask[cur_i] || continue
        cur = ir[cur_i]
        predicate(cur) && return false
        recurse(cur) || continue
        for arg_i in Graphs.outneighbors(ir.dependency_graph, cur_i)
            mask[arg_i] = true
        end
    end
    return false
end

"""
    $TYPEDEF

A struct similar to [`SymbolicUtils.Substituter`](@ref) which leverages the information
in a [`SymbolicUtils.IRStructure`](@ref) to provide a faster implementation of substitution.
This may mutate the wrapped `IRStructure`. Note that `IRSubstituter` is restricted to working
on substitution rules mapping `BasicSymbolic{T}` to `BasicSymbolic{T}`.
"""
struct IRSubstituter{Fold, T, D <: AbstractDict{BasicSymbolic{T}, BasicSymbolic{T}}, F} <: Substituter{Fold}
    ir::IRStructure{T}
    rules::D
    filterer::F
    cache::Dict{Int, Int}
    reachability::Vector{Int}
end

"""
    $TYPEDSIGNATURES

Create an `IRSubstituter` using the given `ir` and `rules`.
"""
function IRSubstituter{Fold}(
        ir::IRStructure{T}, rules::D; filterer::F = default_substitute_filter
    ) where {Fold, T, D <: AbstractDict, F}
    IRSubstituter{Fold, T, D, F}(ir, rules, filterer, Dict{Int, Int}(), Int[])
end

get_substitution_dict(sub::IRSubstituter) = sub.rules
clear_cache!(sub::IRSubstituter) = empty!(sub.cache)


"""
    $TYPEDSIGNATURES

Perform the substitution on element `idx` in the IR, returning the index of the new
element.
"""
function substitute_ir!(sub::IRSubstituter{Fold, T}, idx::Int) where {Fold, T}
    (; rules, filterer, ir) = sub

    # Check the cache, filter, and rules for `idx`
    cached = get(sub.cache, idx, 0)
    iszero(cached) || return cached
    idxsym = ir[idx]
    other = get(rules, idxsym, nothing)
    if other isa BasicSymbolic{T}
        return sub.cache[idx] = populate_ir!(ir, other)
    end
    if !filterer(idxsym)
        return sub.cache[idx] = idx
    end
    if !iscall(idxsym)
        return sub.cache[idx] = idx
    end

    # Now, it's _possible_ `idx` is changed by the substitution

    # `modified` keeps track of which reachable indices from `idx` are modified by the
    # substitution
    modified = get_cached_mask!(ir, length(ir))
    # Queue of indices that are modified but the modified version isn't present in the IR
    # (needs to be computed)
    queue = get_cached_idxs!(ir)
    empty!(queue)
    reachability = sub.reachability
    empty!(reachability)
    get_reachability!(reachability, ir, idx)
    for i in reachability
        # Check the cache, filter, and rules for `i`
        cached = get(sub.cache, i, 0)
        if !iszero(cached) && cached != i
            modified[i] = true
            continue
        end

        sym = ir[i]
        other = get(rules, sym, nothing)
        if other isa BasicSymbolic{T}
            sub.cache[i] = populate_ir!(ir, other)
            modified[i] = true
            continue
        end
        if !filterer(sym)
            sub.cache[i] = i
            continue
        end
        if !iscall(sym)
            sub.cache[i] = i
            continue
        end

        # We will already have processed the children since we're iterating
        # reachable nodes in topological order (dependencies before dependents)
        children = Graphs.outneighbors(ir.dependency_graph, i)
        # If none of the children are modified, `i` isn't modified and we can skip it
        if !any(Base.Fix1(getindex, modified), children)
            sub.cache[i] = i
            continue
        end
        # We need to find the updated expression and insert it into `ir`
        modified[i] = true
        push!(queue, i)
    end

    # The reason we used a queue is that it is possible for `idx` to remain unmodified.
    # This avoids unnecessary work substituting the intermediates only for `idx` to
    # be skipped since the children are all filtered out. As a result, this method is
    # very useful for sparse substitutions.
    children = Graphs.outneighbors(ir.dependency_graph, idx)
    if !any(Base.Fix1(getindex, modified), children)
        return sub.cache[idx] = idx
    end
    push!(queue, idx)

    for i in queue
        # Process the queue
        i_sym = ir[i]
        # Get the new `args` using `new_children`
        args = copy(parent(arguments(i_sym)))
        # `Fold` is a type parameter, so we statically elide the `can_fold` checking
        # if we don't need it.
        if Fold
            can_fold = true
        end
        for j in eachindex(args)
            new_child = args[j] = ir[sub.cache[ir[args[j]]]]
            if Fold
                can_fold &= isconst(new_child)
            end
        end
        op = operation(i_sym)
        if op isa BasicSymbolic{T}
            op_i = ir[op]
            op = ir[sub.cache[op_i]]
            if isconst(op)
                op = unwrap_const(op)
            elseif Fold
                can_fold = false
            end
        end
        # Get the new symbolic expression
        newsym = if Fold
            can_fold &= !(op isa BasicSymbolic{T})
            combine_fold(T, op, args, metadata(i_sym), can_fold)::BasicSymbolic{T}
        else
            maketerm(BasicSymbolic{T}, op, args, metadata(i_sym))::BasicSymbolic{T}
        end

        sub.cache[i] = populate_ir!(ir, newsym)
    end

    # `idx` was in the queue, so it is now in the cache
    return sub.cache[idx]
end

function (sub::IRSubstituter{Fold, T})(expr::BasicSymbolic{T}) where {Fold, T}
    rules = sub.rules
    filterer = sub.filterer
    ir = sub.ir

    idx = populate_ir!(ir, expr)
    newidx = substitute_ir!(sub, idx)
    return ir[newidx]
end

