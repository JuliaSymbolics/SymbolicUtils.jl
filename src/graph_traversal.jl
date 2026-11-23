struct RecursiveDFS{G, N, E, X}
    graph::G
    visited::BitVector
    neighbors_fn::N
    on_enter::E
    on_exit::X
end

function RecursiveDFS(
        g::G; neighbors_fn::N = Graphs.outneighbors,
        on_enter::E = Returns(nothing), on_exit::X = Returns(nothing),
        visited::BitVector = falses(Graphs.nv(g))
    ) where {G <: Graphs.AbstractGraph, N, E, X}
    return RecursiveDFS{G, N, E, X}(g, visited, neighbors_fn, on_enter, on_exit)
end

function (rdfs::RecursiveDFS)(cur::Integer)
    (; graph, visited, neighbors_fn, on_enter, on_exit) = rdfs
    visited[cur] && return
    visited[cur] = true
    on_enter(cur)
    for nbor in neighbors_fn(graph, cur)
        rdfs(nbor)
    end
    on_exit(cur)
    return nothing
end

struct PushToBuffer{T} <: Function
    buffer::Vector{T}
end

(ptb::PushToBuffer)(val) = push!(ptb.buffer, val)

struct FilteredNeighbors{F, N} <: Function
    filter::F
    nbors::N
end

function (fn::FilteredNeighbors)(graph::Graphs.AbstractGraph, i::Integer)
    return Iterators.filter(fn.filter, fn.nbors(graph, i))
end
