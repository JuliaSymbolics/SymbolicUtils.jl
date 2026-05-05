# WARN: `IRStructure` should NOT subtype `AbstractArray`, or this will cause
# invalidations/ambiguities due to symbolic array `getindex`.

"""
    $TYPEDEF

Linear IR representation of a (collection of) symbolic expressions. This can be used to
accelerate operations such as `search_variables!` if frequently performed on the same/similar
expressions.

# Invariants

The `dependency_graph` correctly encodes the argument structure of every expression in the
IR. No ordering constraint is imposed on the indices of expressions and their arguments.

## Extended help

The following details are internal

### Fields

$TYPEDFIELDS
"""
struct IRStructure{T}
    """
    Dependency graph (DAG), where `Graphs.outneighbors(g, v)` denotes the nodes that the
    expression at index `v` depends on. In other words, `outneighbors` is the analogue of
    `arguments`.

    Specifically, `outneighbors` is guaranteed to have the same order as `arguments`. In
    case the operation is also symbolic, it will prefix the neighbors corresponding to the
    arguments. This invariant is maintained even when the canonical form is broken.
    """
    dependency_graph::OrderedDiGraph{Int32}
    """
    Mapping from linear indices to the expression at that index.
    """
    symbols::Vector{BasicSymbolic{T}}
    """
    Inverse mapping of `symbols`.
    """
    definition::IdDict{BasicSymbolic{T}, Int32}
    """
    Map from expressions to all nodes they are `isequal` to. This is not `definition` since
    that uses `===` equality.
    """
    weak_definitions::Dict{BasicSymbolic{T}, Vector{Int32}}
    """
    A cached `BitVector` to be used for several operations supported by this struct. It
    is required for many common operations, and `fill!(false, cached_mask)` is much faster
    than allocating a new one of the appropriate size.
    """
    cached_mask::BitVector
    """
    Similar to `cached_mask` but a `Vector{Int32}`.
    """
    cached_idxs::Vector{Int32}
    """
    Flag indicating whether the struct is in canonical form. Canonical form implies that
    for an expression `ex` at index `idx` in `ir::IRStructure`, there exists an edge
    from `idx` to `ir[arguments(ex)[j]]` for all valid `j` and that
    `arguments(ex)[j] === ir[ir[arguments(ex)[j]]]`. This is typically broken by
    [`SymbolicUtils.replace_node!`](@ref). The graph invariants are still maintained
    after the canonical form is broken.
    """
    is_canonical::Base.RefValue{Bool}
end

"""
    $TYPEDSIGNATURES

Create an empty `IRStructure` to store `BasicSymbolic{T}` expressions.
"""
function IRStructure{T}() where {T}
    ir = IRStructure{T}(
        OrderedDiGraph{Int32}(), BasicSymbolic{T}[],
        IdDict{BasicSymbolic{T}, Int32}(), Dict{BasicSymbolic{T}, Vector{Int32}}(),
        BitVector(), Int32[], Ref{Bool}(true)
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

Get the cached `Vector{Int32}` inside IR.
"""
function get_cached_idxs!(ir::IRStructure)
    return ir.cached_idxs
end

struct IRStructureNotCanonicalError <: Exception
end

function Base.showerror(io::IO, err::IRStructureNotCanonicalError)
    print(io, """
    This operation requires the `IRStructure` to be in canonical form. Canonical form \
    is typically broken when `SymbolicUtils.replace_node!` is used. Prefer using \
    `SymbolicUtils.IRSubstituter` to maintain canonical form at the cost of performance.
    """)
end

@noinline function require_canonical(ir::IRStructure)
    ir.is_canonical[] && return
    throw(IRStructureNotCanonicalError())
end

"""
    $TYPEDSIGNATURES

Compute the transitive closure of `dependency_graph` from node `idx` via DFS postorder,
returning a topologically sorted `Vector{Int32}` of all node indices that `idx` (directly or
indirectly) depends on. Dependencies (children) appear before the expressions that depend on
them (parents). Writes the result to and returns `reachability`.

This function allocates its own scratch space and does not use `ir.cached_mask` or
`ir.cached_idxs`, so it is safe to call even when those are held by an outer caller.
"""
function get_reachability!(reachability::Vector{Int32}, ir::IRStructure, idx::Int32)
    g = ir.dependency_graph
    rdfs = RecursiveDFS(g; on_exit = PushToBuffer(reachability))
    n = length(ir)
    sizehint!(reachability, n)
    rdfs.visited[idx] = true
    for nbor in Graphs.outneighbors(g, idx)
        rdfs.visited[nbor] && continue
        rdfs(nbor)
    end
    return reachability
end

"""
    $TYPEDSIGNATURES

Out-of-place version of [`get_reachability!`](@ref).
"""
get_reachability(ir::IRStructure, idx::Int32) = get_reachability!(Int32[], ir, idx)

"""
    $TYPEDSIGNATURES

Preallocate space for `n` nodes in `ir`.
"""
function Base.sizehint!(ir::IRStructure, n::Integer)
    sizehint!(ir.symbols, n)
    sizehint!(ir.definition, n)
    sizehint!(ir.weak_definitions, n)
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

function _print_ssa_var(io::IO, i::Int32)
    printstyled(io, "%", i; color = :yellow)
end

"""
    $TYPEDSIGNATURES

Print the IR representation of `ir` to `io`, showing at most `limit` statements.
If the IR has more statements than `limit`, the remaining statements are truncated
and a summary line is printed instead. Pass `limit = nothing` to print all statements.

See also [`SymbolicUtils.print_ir`](@ref) which defaults to printing all statements.
"""
function _show_ir(io::IO, ir::IRStructure; limit::Union{Integer, Nothing} = 50)
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
    indeg = zeros(Int32, n)
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
    new_idx = zeros(Int32, n)
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
    # `outneighbors`
    expr_uses = Int32[]
    if iscall(expr)
        # `op` must be processed before `args` to maintain the `outneighbors` ordering
        # invariant: op prefixes the arg neighbors when op isa BasicSymbolic{T}.
        op = operation(expr)
        if op isa BasicSymbolic{T}
            op_idx = populate_ir!(ir, op)
            push!(expr_uses, op_idx)
        end
        args = parent(arguments(expr))
        sizehint!(expr_uses, length(args))
        @union_split_smallvec args for arg in args
            # Add each argument to the IR. This is effectively a postorder traversal.
            arg_idx = populate_ir!(ir, arg)
            push!(expr_uses, arg_idx)
        end
    end
    # Edges are added in argument order to preserve the outneighbors == arguments invariant.
    Graphs.add_vertex!(ir.dependency_graph)
    idx = Graphs.nv(ir.dependency_graph)
    for dst in expr_uses
        Graphs.add_edge!(ir.dependency_graph, idx, dst)
    end
    empty!(expr_uses)
    # Add `expr` to the IR
    push!(ir.symbols, expr)

    buffer = get!(Returns(expr_uses), ir.weak_definitions, expr)
    push!(buffer, idx)

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
        buffer = get!(() -> Int32[], new_ir.weak_definitions, sym)
        push!(buffer, inew)

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

struct IRStructureSearchBuffer{T, S <: AbstractSet{BasicSymbolic{T}}} <: AbstractSet{BasicSymbolic{T}}
    ir::IRStructure{T}
    buffer::S
    searched::BitSet
end

function IRStructureSearchBuffer(ir::IRStructure{T}, buffer::S) where {T, S <: AbstractSet{BasicSymbolic{T}}}
    return IRStructureSearchBuffer{T, S}(ir, buffer, BitSet())
end

Base.length(s::IRStructureSearchBuffer) = length(s.buffer)
Base.iterate(s::IRStructureSearchBuffer, state...) = iterate(s.buffer, state...)
Base.in(x::BasicSymbolic{T}, s::IRStructureSearchBuffer{T}) where {T} = in(x, s.buffer)

function Base.empty(s::IRStructureSearchBuffer{T, S}) where {T, S}
    return IRStructureSearchBuffer{T, S}(s.ir, empty(s.buffer), empty(s.searched))
end

function Base.push!(s::IRStructureSearchBuffer{T}, x::BasicSymbolic{T}) where {T}
    push!(s.buffer, x)
    return s
end

Base.keytype(::Type{I}) where {T, I <: IRStructureSearchBuffer{T}} = BasicSymbolic{T}

function Base.delete!(s::IRStructureSearchBuffer{T}, x::BasicSymbolic{T}) where {T}
    was_in_buffer = x in s.buffer
    delete!(s.buffer, x)
    was_in_buffer || return s
    # Deleting invalidates the cache. Find all nodes `isequal` to this one.
    defs = get(s.ir.weak_definitions, x, nothing)
    defs isa Vector{Int32} || return s
    # Go through `defs`, walk the dependency tree backwards and delete any entries in
    # `s.searched` that we find.
    rdfs = RecursiveDFS(
        s.ir.dependency_graph;
        neighbors_fn = FilteredNeighbors(in(s.searched), Graphs.inneighbors),
        on_exit = Base.Fix1(delete!, s.searched)
    )
    for def in defs
        def in s.searched || continue
        rdfs(def)
    end
    return s
end

function Base.setdiff!(s::IRStructureSearchBuffer{T}, ss...) where {T}
    idxs = get_cached_idxs!(s.ir)
    empty!(idxs)
    for other in ss
        for x in other
            was_in_buffer = x in s.buffer
            delete!(s.buffer, x)
            was_in_buffer || continue
            defs = get(s.ir.weak_definitions, x, nothing)
            if defs isa Vector{Int32}
                append!(idxs, defs)
            end
        end
    end
    isempty(idxs) && return s
    rdfs = RecursiveDFS(
        s.ir.dependency_graph;
        neighbors_fn = FilteredNeighbors(in(s.searched), Graphs.inneighbors),
        on_exit = Base.Fix1(delete!, s.searched)
    )
    for idx in idxs
        def in s.searched || continue
        rdfs(idx)
    end
    return s
end

function Base.filter!(pred::F, s::IRStructureSearchBuffer{T}) where {F, T}
    idxs = get_cached_idxs!(s.ir)
    empty!(idxs)

    for x in s
        pred(x) && continue
        delete!(s.buffer, x)
        defs = get(s.ir.weak_definitions, x, nothing)
        if defs isa Vector{Int32}
            append!(idxs, defs)
        end
    end
    isempty(idxs) && return s
    rdfs = RecursiveDFS(
        s.ir.dependency_graph;
        neighbors_fn = FilteredNeighbors(in(s.searched), Graphs.inneighbors),
        on_exit = Base.Fix1(delete!, s.searched)
    )
    for idx in idxs
        def in s.searched || continue
        rdfs(idx)
    end
    return s
end

function search_variables!(
        buffer::IRStructureSearchBuffer{T, S}, expr::BasicSymbolic{T};
        is_atomic::F = default_is_atomic, recurse::G = iscall
    ) where {T, S, F, G}
    if is_atomic(expr)
        push!(buffer, expr)
        return
    end
    recurse(expr) || return
    # We call `populate_ir!` late because it's possible that `recurse` filters
    # out a big expression before we have to put it into the IR.
    ir = buffer.ir
    idx = populate_ir!(ir, expr)
    idx in buffer.searched && return

    mask = get_cached_mask!(ir, length(ir))
    for arg_i in Graphs.outneighbors(ir.dependency_graph, idx)
        mask[arg_i] = true
    end

    reachability = get_cached_idxs!(ir)
    empty!(reachability)
    get_reachability!(reachability, ir, idx)
    for cur_i in Iterators.reverse(reachability)
        mask[cur_i] || continue
        cur_i in buffer.searched && continue
        push!(buffer.searched, cur_i)
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

    push!(buffer.searched, idx)

    return nothing
end

"""
    $TYPEDSIGNATURES

Optimized version of [`SymbolicUtils.search_variables!`](@ref) that leverages the provided
[`SymbolicUtils.IRStructure`](@ref). May also add `expr` to `ir` in the process.
"""
function search_variables!(
        buffer::AbstractSet{BasicSymbolic{T}}, ir::IRStructure{T}, expr::BasicSymbolic{T};
        is_atomic::F = default_is_atomic, recurse::G = iscall
    ) where {T, F, G}
    search_variables!(IRStructureSearchBuffer(ir, buffer), expr; is_atomic, recurse)
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
    cache::Dict{Int32, Int32}
    reachability::Vector{Int32}
end

"""
    $TYPEDSIGNATURES

Create an `IRSubstituter` using the given `ir` and `rules`.
"""
function IRSubstituter{Fold}(
        ir::IRStructure{T}, rules::D; filterer::F = default_substitute_filter
    ) where {Fold, T, D <: AbstractDict, F}
    IRSubstituter{Fold, T, D, F}(ir, rules, filterer, Dict{Int32, Int32}(), Int32[])
end

get_substitution_dict(sub::IRSubstituter) = sub.rules
clear_cache!(sub::IRSubstituter) = empty!(sub.cache)


"""
    $TYPEDSIGNATURES

Perform the substitution on element `idx` in the IR, returning the index of the new
element.
"""
function substitute_ir!(sub::IRSubstituter{Fold, T}, idx::Int32) where {Fold, T}
    # Substitution requires checking if argument expressions are present in the
    # substitution rules. If canonical form is violated, the symbolic expressions
    # are not necessarily accurate and thus substitution cannot be guaranteed to
    # work correctly.
    require_canonical(sub.ir)

    (; rules, filterer, ir) = sub

    # Check the cache, filter, and rules for `idx`
    cached = get(sub.cache, idx, zero(Int32))
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
        cached = get(sub.cache, i, zero(Int32))
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

"""
    $TYPEDSIGNATURES

Replace the expression `old` in `ir` with the expression `new`. `old` must already exist in `ir`.
Note that this is not symbolic substitution, since any expressions that depend on `old` will not
be updated. This will simply update the internal graph data structure such that the expression
at `old` is now `new`, and the arguments of `new` form the out-neighbors of the vertex. This breaks
the canonical form of `ir`.
"""
function replace_node!(ir::IRStructure{T}, old::BasicSymbolic{T}, new::BasicSymbolic{T}) where {T}
    ir.is_canonical[] = false
    idx = ir[old]
    ir.symbols[idx] = new
    delete!(ir.definition, old)
    weakdefs = ir.weak_definitions[old]
    filter!(!isequal(idx), weakdefs)
    isempty(weakdefs) && delete!(ir.weak_definitions, old)

    buffer = get!(() -> Int32[], ir.weak_definitions, new)
    push!(buffer, idx)

    iszero(Graphs.outdegree(ir.dependency_graph, idx)) && return

    rem_outedges!(ir.dependency_graph, idx)
    op = operation(new)
    if op isa BasicSymbolic{T}
        Graphs.add_edge!(ir.dependency_graph, idx, populate_ir!(ir, op))
    end
    args = parent(arguments(new))
    @union_split_smallvec args for arg in args
        Graphs.add_edge!(ir.dependency_graph, idx, populate_ir!(ir, arg))
    end
    return nothing
end

