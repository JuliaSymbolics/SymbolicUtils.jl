"""
    $TYPEDEF

A directed graph that wraps `Graphs.SimpleDiGraph` and remembers edge insertion order.
`Graphs.outneighbors(g, v)` returns the out-neighbors of `v` in the order edges were
added, rather than in sorted order.

All other graph operations (`inneighbors`, `topological_sort_by_dfs`, etc.) are
delegated to the underlying `SimpleDiGraph`.
"""
struct OrderedDiGraph <: Graphs.AbstractGraph{Int}
    graph::Graphs.SimpleDiGraph{Int}
    """
    Out-neighbors of each vertex in edge-insertion order.
    """
    ordered_outneighbors::Vector{Vector{Int}}
end

OrderedDiGraph() = OrderedDiGraph(Graphs.SimpleDiGraph{Int}(), Vector{Int}[])

Graphs.is_directed(::Type{OrderedDiGraph}) = true
Graphs.nv(g::OrderedDiGraph) = Graphs.nv(g.graph)
Graphs.ne(g::OrderedDiGraph) = Graphs.ne(g.graph)
Graphs.vertices(g::OrderedDiGraph) = Graphs.vertices(g.graph)
Graphs.edges(g::OrderedDiGraph) = Graphs.edges(g.graph)
Graphs.has_vertex(g::OrderedDiGraph, v) = Graphs.has_vertex(g.graph, v)
Graphs.has_edge(g::OrderedDiGraph, s, d) = Graphs.has_edge(g.graph, s, d)
Graphs.inneighbors(g::OrderedDiGraph, v) = Graphs.inneighbors(g.graph, v)
Graphs.outneighbors(g::OrderedDiGraph, v) = g.ordered_outneighbors[v]

function Graphs.add_vertex!(g::OrderedDiGraph)
    Graphs.add_vertex!(g.graph) || return false
    push!(g.ordered_outneighbors, Int[])
    return true
end

function Graphs.add_vertices!(g::OrderedDiGraph, n::Integer)
    Graphs.add_vertices!(g.graph, n)
    for _ in 1:n
        push!(g.ordered_outneighbors, Int[])
    end
    return n
end

function Graphs.add_edge!(g::OrderedDiGraph, src::Integer, dst::Integer)
    Graphs.add_edge!(g.graph, src, dst) || return false
    push!(g.ordered_outneighbors[src], dst)
    return true
end

function Graphs.rem_vertex!(g::OrderedDiGraph, v::Integer)
    # Only removing the last vertex is supported. The sole caller (rollback!) always
    # removes vertices in reverse order, so this fast path is always taken.
    v == Graphs.nv(g) ||
        throw(ArgumentError("OrderedDiGraph only supports removing the last vertex"))
    Graphs.rem_vertex!(g.graph, v) || return false
    pop!(g.ordered_outneighbors)
    return true
end

function Graphs.rem_edge!(g::OrderedDiGraph, src::Integer, dst::Integer)
    Graphs.rem_edge!(g.graph, src, dst) || return false
    idx = findfirst(==(dst), g.ordered_outneighbors[src])
    idx !== nothing && deleteat!(g.ordered_outneighbors[src], idx)
    return true
end

Graphs.topological_sort_by_dfs(g::OrderedDiGraph) =
    Graphs.topological_sort_by_dfs(g.graph)
