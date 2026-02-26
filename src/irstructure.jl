# WARN: `IRStructure` should NOT subtype `AbstractArray`, or this will cause
# invalidations/ambiguities due to symbolic array `getindex`.

"""
    $TYPEDEF

Linear IR representation of a (collection of) symbolic expressions. This can be used to
accelerate operations such as `search_variables!` if frequently performed on the same/similar
expressions.

# Invariants

For every expression in the IR, if it is present at index `i`, then all of its arguments
are present with indices `< i`

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
    """
    dependency_graph::Graphs.SimpleDiGraph{Int}
    """
    Mapping from linear indices to the expression at that index.
    """
    symbols::Vector{BasicSymbolic{T}}
    """
    Inverse mapping of `symbols`.
    """
    definition::Dict{BasicSymbolic{T}, Int}
    """
    The transitive closure of `dependency_graph`, indicating all of the nodes that a given
    node (directly or indirectly) depends on. The inverse mapping is not maintained.
    Each inner vector is sorted.
    """
    reachability::Vector{Vector{Int}}
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
        Graphs.SimpleDiGraph{Int}(), BasicSymbolic{T}[],
        Dict{BasicSymbolic{T}, Int}(), Vector{Int}[], BitVector(), Int[]
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

"""
    $TYPEDSIGNATURES

Preallocate space for `n` nodes in `ir`.
"""
function Base.sizehint!(ir::IRStructure, n::Integer)
    sizehint!(ir.symbols, n)
    sizehint!(ir.definition, n)
    sizehint!(ir.reachability, n)
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
    resize!(ir.reachability, bm)
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
    # `outneighbors`
    expr_uses = Int[]
    # transitive closure
    reachables = Int[]
    if iscall(expr)
        args = parent(arguments(expr))
        # This avoids a lot of allocations
        sizehint!(expr_uses, length(args))
        sizehint!(reachables, 2length(ir.symbols))
        @union_split_smallvec args for arg in args
            # Add each argument to the IR. This is effectively a postorder traversal.
            arg_idx = populate_ir!(ir, arg)
            push!(expr_uses, arg_idx)
            # Add everything for now
            append!(reachables, ir.reachability[arg_idx])
            push!(reachables, arg_idx)
        end
        op = operation(expr)
        if op isa BasicSymbolic{T}
            op_idx = populate_ir!(ir, op)
            push!(expr_uses, op_idx)
            append!(reachables, ir.reachability[op_idx])
            append!(reachables, op_idx)
        end
    end
    # Sorting ensures `add_edge!` is a `push!`
    sort!(expr_uses)
    Graphs.add_vertex!(ir.dependency_graph)
    idx = Graphs.nv(ir.dependency_graph)
    for dst in expr_uses
        Graphs.add_edge!(ir.dependency_graph, idx, dst)
    end
    # Add `expr` to the IR
    push!(ir.symbols, expr)
    # `sort! ∘ unique!` is faster
    sort!(reachables)
    unique!(reachables)
    push!(ir.reachability, reachables)
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
    # Since everything is sorted and we have the transitive closure, all that is
    # necessary is to union all the transitive closures and add those expressions
    # to `new_ir` in order.
    #
    # This is a `BitVector` because iterating over it is equivalent in time complexity
    # to iterating over `ir`, and it iterates elements in sorted order. `SortedSet`
    # and `Set + collect + sort` are `O(n * log(n))` where `n` can be close to
    # `length(ir)`.
    reachables = get_cached_mask!(ir, length(ir))
    first_reachable = length(reachables)
    for expr in exprs
        expr_i = get(ir.definition, expr, 0)
        iszero(expr_i) && _throw_expr_not_in_ir(expr)
        reachables[expr_i] = true
        first_reachable = min(first_reachable, expr_i, first(ir.reachability[expr_i]))
        reachables[ir.reachability[expr_i]] .= true
    end
    
    n_new_verts = count(reachables)
    Graphs.add_vertices!(new_ir.dependency_graph, n_new_verts)
    sizehint!(new_ir, n_new_verts)

    # Instead of calling `populate_ir!`, we can directly build the new IR
    inew = 0
    for iold in first_reachable:length(reachables)
        reachables[iold] || continue
        inew += 1
        # Add expression to the IR
        sym = ir.symbols[iold]
        push!(new_ir.symbols, sym)
        new_ir.definition[sym] = inew

        # Translate old neighbors to new ones. Since we're iterating
        # `reachables` in sorted order, we can guarantee that these
        # have already been added to `new_ir`.
        oldnbors = Graphs.outneighbors(ir.dependency_graph, iold)
        for nbor in oldnbors
            nsym = ir.symbols[nbor]
            nbor_idx = new_ir.definition[nsym]
            Graphs.add_edge!(new_ir.dependency_graph, inew, nbor_idx)
        end

        # Same as previous, but for the transitive closure.
        ireachables = Int[]
        sizehint!(ireachables, length(ir.reachability[iold]))
        for oldv in ir.reachability[iold]
            rsym = ir.symbols[oldv]
            vert_idx = new_ir.definition[rsym]
            push!(ireachables, vert_idx)
        end
        push!(new_ir.reachability, ireachables)
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
        push!(buffer. expr)
        return
    end
    recurse(expr) || return
    idx = populate_ir!(ir, expr)
    # We don't have a fast path here, since `is_atomic` also prevents recursing into
    # subtrees. Thus, we always have to use the general BFS approach.

    # This is basically equivalent to a BFS, since `recurse` may filter out sections of the
    # DAG which means we can't just iterate over the reachable vertices.
    mask = get_cached_mask!(ir, idx)
    for arg_i in Graphs.outneighbors(ir.dependency_graph, idx)
        mask[arg_i] = true
    end

    for cur_i in Iterators.reverse(ir.reachability[idx])
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
    # Fast path when we know we don't have to filter out subtrees
    if recurse === iscall
        for i in ir.reachability[idx]
            predicate(ir.symbols[i]) && return true
        end

        return false
    end
    
    # Similar to BFS in `search_variables!`
    mask = get_cached_mask!(ir, idx)
    for arg_i in Graphs.outneighbors(ir.dependency_graph, idx)
        mask[arg_i] = true
    end

    for cur_i in Iterators.reverse(ir.reachability[idx])
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
end

"""
    $TYPEDSIGNATURES

Create an `IRSubstituter` using the given `ir` and `rules`.
"""
function IRSubstituter{Fold}(
        ir::IRStructure{T}, rules::D; filterer::F = default_substitute_filter
    ) where {Fold, T, D <: AbstractDict, F}
    IRSubstituter{Fold, T, D, F}(ir, rules, filterer, Dict{Int, Int}())
end

get_substitution_dict(sub::IRSubstituter) = sub.rules

"""
    $TYPEDSIGNATURES

Check the preconditions for substituting the expression at index `i`. If it exists in cache,
is filtered out, or present in the rules, this will return the index of the new expression
to use. If none of those conditions are satisfied and `__substitute_ir_element!` is required
to find the index of the new expression, returns `0`. Used by `substitute_ir!`.
"""
function __check_substitution_conditions!(sub::IRSubstituter{Fold, T}, i::Int) where {Fold, T}
    (; rules, filterer, ir) = sub
    # Check the cache, filter, and rules for `i`
    cached = get(sub.cache, i, 0)
    iszero(cached) || return cached

    sym = ir[i]
    if !filterer(sym)
        return sub.cache[i] = i
    end

    other = get(rules, sym, nothing)
    if other isa BasicSymbolic{T}
        return sub.cache[i] = populate_ir!(ir, other)
    end

    if !iscall(sym)
        return sub.cache[i] = i
    end

    # We haven't substituted `i` before, it isn't filtered out and it isn't directly
    # in the rules.
    return 0
end

"""
    $TYPEDSIGNATURES

Used by `substitute_ir!`. Does not check cache/filter/rules, but simply performs the
substitution assuming `idx` points to an `iscall` symbolic. Returns the index of the
substituted symbolic expression.
"""
function __substitute_ir_element!(sub::IRSubstituter{Fold, T}, i::Int) where {Fold, T}
    (; rules, filterer, ir) = sub

    is_dirty = false
    children = Graphs.outneighbors(ir.dependency_graph, i)
    for (j, c) in enumerate(children)
        # Children have already been substituted, so we just check the cache
        newchild = get(sub.cache, c, c)
        is_dirty |= c != newchild
    end

    # If we didn't change anything, exit
    if !is_dirty
        return sub.cache[i] = i
    end

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
    # Get the new symbolic expression
    newsym = if Fold
        can_fold &= !(op isa BasicSymbolic{T})
        combine_fold(T, op, args, metadata(i_sym), can_fold)::BasicSymbolic{T}
    else
        maketerm(BasicSymbolic{T}, op, args, metadata(i_sym))::BasicSymbolic{T}
    end

    return sub.cache[i] = populate_ir!(ir, newsym)
end

"""
    $TYPEDSIGNATURES

Perform the substitution on element `idx` in the IR, returning the index of the new
element.
"""
function substitute_ir!(sub::IRSubstituter{Fold, T}, idx::Int) where {Fold, T}
    (; rules, filterer, ir) = sub

    # Check if we have a trivial solution for `idx` and can early-exit.
    result = __check_substitution_conditions!(sub, idx)
    iszero(result) || return result

    # Go through the transitive closure of `idx` in order (so we process a node
    # only after processing its children) and substitute them.
    for i in ir.reachability[idx]
        # Same checking process for each element
        i_result = __check_substitution_conditions!(sub, i)
        if !iszero(i_result)
            sub.cache[i] = i_result
            continue
        end

        # Update the cache with the substituted version of `i`.
        __substitute_ir_element!(sub, i)
    end

    # Return the substituted version of `idx`.
    return __substitute_ir_element!(sub, idx)
end

function (sub::IRSubstituter{Fold, T})(expr::BasicSymbolic{T}) where {Fold, T}
    rules = sub.rules
    filterer = sub.filterer
    ir = sub.ir

    idx = populate_ir!(ir, expr)
    newidx = substitute_ir!(sub, idx)
    return ir[newidx]
end

