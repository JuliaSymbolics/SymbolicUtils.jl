using DataStructures
export EGraph, touch!, rebuild!, saturate!

# ids are just UInt64
const Id = UInt64

# An Id as a Symbolic node
struct EID{T} <: Symbolic{T}
    id::Id
    dependents::Set # All the enodes who have this as their children
end
Base.hash(e::EID, u::UInt) = hash(xor(e.id, 0xe1de1de1de1de1de), u)
Base.isequal(a::EID, b::EID) = a.id == b.id
gen_id(graph) = graph.node_counter[] += 1
EID(graph, node) = EID{symtype(node)}(gen_id(graph), Set([]))
is_eid(t) = t isa EID
Base.show(io::IO, n::EID) = print(io, "~", Int(n.id))

# ID Set maintains a canonical Id, and a set of equivalent ids
mutable struct IdSet
    canonical_id::EID
    set::Set{EID}
end
Base.isless(eid1, eid2) = isless(eid1.id, eid2.id)
IdSet(set) = IdSet(minimum(set), Set(set))
canonical_id(set::IdSet) = set.canonical_id
function Base.union(set1::IdSet, set2::IdSet)
    IdSet(min(set1.canonical_id, set2.canonical_id), union(set1.set, set2.set))
end

function Base.union!(set1::IdSet, set2::IdSet)
    set1.canonical_id = min(set1.canonical_id, set2.canonical_id)
    set1.set = union!(set1.set, set2.set)
end

function Base.push!(set::IdSet, x)
    set1.canonical_id = min(set.canonical_id, x)
    push!(set1.set, x)
end

# TODO: MutableBinaryMinHeap can be replaced by a Min value + a Set
# then the Union is also easy -- always chose the lowest as the min value and merge the sets
struct EGraph
    node_counter::Ref{Id}
    union::Dict{EID, IdSet} # Equivalent eclass Ids
    eclasses::Dict{EID, Set} # Id -> eclasses;
                # Here many Ids can map to the same Set, but `union` should give the canonical id
    nodes::Dict{Any, EID} # e-node -> Eclass Id
end

EGraph() = EGraph(Ref{Id}(0), Dict(), Dict(), Dict())

function Base.show(io::IO, g::EGraph)
    eclasses = Dict{EID, Set}()
    if isempty(g.nodes)
        return print(io, "Empty EGraph")
    end
    for (n, id) in g.nodes
        set = Base.get!(Set, eclasses, canonical_id(g.union[id]))
        push!(set, n)
    end
    ks = sort(collect(keys(eclasses)))
    for k in ks
        print(io, Int(k.id), ": ")
        for n in eclasses[k]
            show(io, n)
            print(io, "; ")
        end
        println(io)
    end
end

function term_similarterm(t, f, args, type; metadata=nothing)
    Term{type}(f, args; metadata=metadata)
end

# modifies the `graph` to add an expr to
# to the egraph as an e-node creating the required eclasses
# returns the eclass id and enode
# XXX: Just write the fully unrolled version here
# XXX: Returns: eid, and boolean flag denoting if the node is actually new
function touch!(graph, expr, iscanonical=false)
    # Here we assume all `nodes` in `graph.nodes` map to their canonical ids
    is_eid(expr) && return (expr, false)
    haskey(graph.nodes, expr) && return (graph.nodes[expr], false) # This requires that the nodes have canonical ids as children

    if !iscanonical && istree(expr)
        # canonicalize and try again
        args = map(arguments(expr)) do a
            first(touch!(graph, a))
        end
        expr = term(operation(expr), args..., type=symtype(expr))
        args = foreach(arguments(expr)) do a
            # expr is a parent of
            push!(a.dependents, expr)
        end
        # Check again after canonicalizing
        return touch!(graph, expr, true)
    end

    # new id
    eid = EID(graph, expr)
    graph.nodes[expr] = eid
    graph.union[eid] = IdSet([eid])
    graph.eclasses[eid] = Set([expr])
    return (eid, true)
end

function merge_eids!(graph, eid1, eid2)
    u1, u2 = graph.union[eid1], graph.union[eid2]

    # they are the same
    if u1 === u2 || isequal(canonical_id(u1), canonical_id(u2))
        return canonical_id(u1)
    end

    c_id = min(canonical_id(u1), canonical_id(u2))
    fwd_update = Set{EID}()
    if !isequal(c_id, u1)
        union!(fwd_update, u1.set)
    end
    if !isequal(c_id, u2)
        union!(fwd_update, u2.set)
    end
    setdiff!(fwd_update, [eid1, eid2])

    union!(u1, u2)
    graph.union[eid2] = u1

    for id in fwd_update
        merge_eids!(graph, id, c_id)
    end
    return canonical_id(u1)
end

# match a single node with rule, assume we are not looking at equivalent
# nodes at this point. Just one path of the graph
function saturate!(graph, rules; nodes=graph.nodes)
    # XXX: use rule.depth for recursively evaluating

    saturated = false
    while !saturated
        matches = []
        merge_worklist = []
        saturated = true
        for (node, eid) in nodes
            for rule in rules
                node′ = rule(node)
                if node′ !== nothing && !isequal(node, node′)
                    push!(matches, (eid, node′))
                end
            end
        end
        for (eid, node′) in matches
            eid′, isnew = touch!(graph, node′)
            if isnew
                # XXX: What when an eid′ is an already available node
                # but is not equivalent in class yet to `eid`?
                saturated = false
            end
            push!(merge_worklist, (eid, eid′))
        end
        rebuild!(graph, merge_worklist)
    end
    graph
end

function rebuild!(egraph, worklist)
    while !isempty(worklist)
        (id1, id2) = pop!(worklist)
        # find Ids that are not already equivalent to the left-hand set
        # because we are merging the right-hand into the left hand, and in the process
        # replacing the right hand with the new set
        c_id = merge_eids!(egraph, id1, id2)

        for id in (id1, id2)
            isequal(id, c_id) && continue
            while !isempty(id.dependents)
                node = pop!(id.dependents)
                new_node = substitute(node, Dict(id => c_id))
                push!(c_id.dependents, new_node)
                ## TODO: update `node` to `new_node` everywhere!
            end
        end
    end
end

