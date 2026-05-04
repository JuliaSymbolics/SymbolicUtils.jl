"""
    OrderedDiGraph{T<:Integer}

A directed graph where the forward adjacency list preserves edge insertion
order. Mirrors `Graphs.SimpleDiGraph` with two differences:
- `outneighbors(g, v)` returns neighbors in the order edges were inserted.
- `inneighbors(g, v)` returns an `AdjView` (unordered); membership tests are O(1).

### Adjacency representation

Each entry of `fadjlist` is a `Union{NTuple{2,T}, Vector{T}}`:
- `NTuple{2,T}` for vertices with 0, 1, or 2 out-edges. `zero(T)` is a
  sentinel: `(0,0)` means 0 edges, `(dst,0)` means 1 edge, `(a,b)` (both
  non-zero) means 2 edges. Non-zero entries always occupy the front slots.
- `Vector{T}` once a vertex acquires a third out-edge. The vector is never
  shrunk back to a tuple after removal.

Each entry of `badjlist` is a `Union{NTuple{2,T}, Set{T}}`:
- `NTuple{2,T}` for vertices with 0, 1, or 2 in-edges (same sentinel convention).
- `Set{T}` once a vertex acquires a third in-edge. Never shrunk back to a tuple.

For example, after inserting edges `2 => 3`, `1 => 3`, `1 => 2` in that order:
- `outneighbors(g, 1)` returns `[3, 2]`
- `inneighbors(g, 3)` returns a `Set` containing `{2, 1}` (order unspecified)
"""
mutable struct OrderedDiGraph{T <: Integer} <: Graphs.AbstractGraph{T}
    ne::Int
    fadjlist::Vector{Union{NTuple{2, T}, Vector{T}}}
    badjlist::Vector{Union{NTuple{2, T}, Set{T}}}

    function OrderedDiGraph{T}(
            ne::Int,
            fadjlist::Vector{Union{NTuple{2, T}, Vector{T}}},
            badjlist::Vector{Union{NTuple{2, T}, Set{T}}},
        ) where {T <: Integer}
        return new{T}(ne, fadjlist, badjlist)
    end
end

function OrderedDiGraph(
        ne::Int,
        fadjlist::Vector{Union{NTuple{2, T}, Vector{T}}},
        badjlist::Vector{Union{NTuple{2, T}, Set{T}}},
    ) where {T}
    return OrderedDiGraph{T}(ne, fadjlist, badjlist)
end

#
# Internal helpers for adjacency list entries.
# fadjlist entries are Union{NTuple{2,T}, Vector{T}}.
# badjlist entries are Union{NTuple{2,T}, Set{T}}.
#

# Effective length (number of real, non-sentinel neighbors).
@inline _flen(t::NTuple{2, T}) where {T} = iszero(t[1]) ? 0 : iszero(t[2]) ? 1 : 2
@inline _flen(v::Vector) = length(v)
@inline _flen(s::Set) = length(s)

# Indexed access into effective elements (assumes 1 <= i <= _flen(entry)).
# Only valid for NTuple and Vector (not Set, which is unordered).
@inline _fget(t::NTuple{2}, i::Int) = t[i]
@inline _fget(v::Vector, i::Int) = v[i]

# Membership test. Assumes x is a valid (non-zero) vertex index.
@inline _fin(t::NTuple{2, T}, x) where {T} = t[1] == x || t[2] == x
@inline _fin(v::Vector, x) = x in v
@inline _fin(s::Set, x) = x in s

#
# AdjView{T}: lightweight non-allocating view over an adjacency list entry.
# The entry field stores one of three concrete backing types:
#   NTuple{2,T} — 0–2 neighbors (small case, no heap allocation)
#   Vector{T}   — 3+ out-neighbors (fadjlist after transition)
#   Set{T}      — 3+ in-neighbors  (badjlist after transition)
#
# Storing the union inside the struct (rather than as a type parameter) means
# outneighbors and inneighbors both return the single concrete type AdjView{T},
# avoiding a Union return type at call sites.  Efficiency is recovered by
# manually union-splitting on entry type inside each method: isa checks let the
# compiler specialize each branch.  All three backing types use Int as their
# iteration state, so the inferred state type is concrete across all branches.
#

struct AdjView{T <: Integer}
    entry::Union{NTuple{2, T}, Vector{T}, Set{T}}
end

Base.eltype(::Type{AdjView{T}}) where {T} = T

# length and membership dispatch through _flen / _fin (defined for all three).
Base.length(v::AdjView) = _flen(v.entry)
Base.in(x, v::AdjView) = _fin(v.entry, x)

# getindex: valid only for ordered backing (NTuple / Vector).
Base.getindex(v::AdjView, i::Int) = _fget(v.entry, i)

# --- iterate: manual union-split on entry type ---
# NTuple and Vector use sequential Int indices as state; Set uses its internal
# hash-table slot index, also an Int.  All branches share Int state so the
# inferred return type is Union{Nothing, Tuple{T, Int}} — no dynamic dispatch.

function Base.iterate(v::AdjView{T}) where {T}
    entry = v.entry
    if entry isa NTuple{2, T}
        _flen(entry) == 0 && return nothing
        return _fget(entry, 1)::T, 2
    elseif entry isa Vector{T}
        isempty(entry) && return nothing
        return @inbounds(entry[1])::T, 2
    else
        return iterate(entry::Set{T})
    end
end

function Base.iterate(v::AdjView{T}, state::Int) where {T}
    entry = v.entry
    if entry isa NTuple{2, T}
        state > _flen(entry) && return nothing
        return _fget(entry, state)::T, state + 1
    elseif entry isa Vector{T}
        state > length(entry) && return nothing
        return @inbounds(entry[state])::T, state + 1
    else
        return iterate(entry::Set{T}, state)
    end
end


#
# Constructors
#

"""
    OrderedDiGraph{T}(n=0)

Construct an `OrderedDiGraph{T}` with `n` vertices and 0 edges.
"""
function OrderedDiGraph{T}(n::Integer = 0) where {T <: Integer}
    z = zero(T)
    fadjlist = Union{NTuple{2, T}, Vector{T}}[(z, z) for _ in Base.OneTo(n)]
    badjlist = Union{NTuple{2, T}, Set{T}}[(z, z) for _ in Base.OneTo(n)]
    return OrderedDiGraph{T}(0, fadjlist, badjlist)
end

OrderedDiGraph(n::T) where {T <: Integer} = OrderedDiGraph{T}(n)
OrderedDiGraph() = OrderedDiGraph{Int}()

"""
    OrderedDiGraph(::Type{T})

Construct an empty `OrderedDiGraph{T}` with 0 vertices and 0 edges.
"""
OrderedDiGraph(::Type{T}) where {T <: Integer} = OrderedDiGraph{T}()

"""
    OrderedDiGraph{T}(g::OrderedDiGraph)

Construct a copy of `g`, converting vertex indices to type `T`.
"""
function OrderedDiGraph{T}(g::OrderedDiGraph) where {T <: Integer}
    fadj = Union{NTuple{2, T}, Vector{T}}[
        entry isa Vector ? Vector{T}(entry) : (T(entry[1]), T(entry[2]))
            for entry in g.fadjlist
    ]
    badj = Union{NTuple{2, T}, Set{T}}[
        entry isa Set ? Set{T}(entry) : (T(entry[1]), T(entry[2]))
            for entry in g.badjlist
    ]
    return OrderedDiGraph{T}(g.ne, fadj, badj)
end

OrderedDiGraph(g::OrderedDiGraph) = Base.copy(g)

"""
    OrderedDiGraph{T}(g::AbstractGraph)
    OrderedDiGraph(g::AbstractGraph)

Construct an `OrderedDiGraph` from any `AbstractGraph` by enumerating its edges.
If `g` is undirected, both directed edges `(u, v)` and `(v, u)` are added.
"""
function OrderedDiGraph{T}(g::Graphs.AbstractGraph) where {T <: Integer}
    h = OrderedDiGraph{T}(Graphs.nv(g))
    for e in Graphs.edges(g)
        Graphs.add_edge!(h, T(Graphs.src(e)), T(Graphs.dst(e)))
        if !Graphs.is_directed(g)
            Graphs.add_edge!(h, T(Graphs.dst(e)), T(Graphs.src(e)))
        end
    end
    return h
end

OrderedDiGraph(g::Graphs.AbstractGraph{T}) where {T} = OrderedDiGraph{T}(g)

#
# Graphs.jl interface
#

Graphs.edgetype(::OrderedDiGraph{T}) where {T} = Graphs.Edge{T}

Graphs.nv(g::OrderedDiGraph{T}) where {T} = T(length(g.fadjlist))

Graphs.ne(g::OrderedDiGraph) = g.ne

Graphs.vertices(g::OrderedDiGraph) = Base.OneTo(Graphs.nv(g))

Graphs.is_directed(::Type{<:OrderedDiGraph}) = true

Graphs.has_vertex(g::OrderedDiGraph, v::Integer) = v in Graphs.vertices(g)

function Graphs.has_edge(g::OrderedDiGraph, s, d)
    verts = Graphs.vertices(g)
    (s in verts && d in verts) || return false
    return _fin(@inbounds(g.badjlist[d]), s)
end

Graphs.outneighbors(g::OrderedDiGraph{T}, v::Integer) where {T} = AdjView{T}(@inbounds g.fadjlist[v])
Graphs.inneighbors(g::OrderedDiGraph{T}, v::Integer) where {T} = AdjView{T}(@inbounds g.badjlist[v])

Base.zero(::Type{OrderedDiGraph{T}}) where {T} = OrderedDiGraph{T}()
Base.zero(g::G) where {G <: OrderedDiGraph} = zero(G)

#
# Edge iteration
#

struct OrderedDiGraphEdgeIter{T <: Integer} <: Graphs.AbstractEdgeIter
    g::OrderedDiGraph{T}
end

Graphs.edges(g::OrderedDiGraph) = OrderedDiGraphEdgeIter(g)

Base.eltype(::Type{OrderedDiGraphEdgeIter{T}}) where {T} = Graphs.Edge{T}
Base.length(it::OrderedDiGraphEdgeIter) = Graphs.ne(it.g)

@inline function Base.iterate(
        it::OrderedDiGraphEdgeIter{T}, state = (one(T), 1)
    ) where {T}
    g = it.g
    n = Graphs.nv(g)
    u, i = state
    n == 0 && return nothing
    return @inbounds while true
        entry = g.fadjlist[u]
        if i > _flen(entry)
            u == n && return nothing
            u += one(T)
            i = 1
            continue
        end
        return Graphs.Edge(u, _fget(entry, i)), (u, i + 1)
    end
end

Base.in(e, it::OrderedDiGraphEdgeIter) = Graphs.has_edge(it.g, e)

function Base.show(io::IO, it::OrderedDiGraphEdgeIter)
    return print(io, "OrderedDiGraphEdgeIter $(Graphs.ne(it.g))")
end

#
# Display and equality
#

function Base.show(io::IO, ::MIME"text/plain", g::OrderedDiGraph{T}) where {T}
    return print(io, "{$(Graphs.nv(g)), $(Graphs.ne(g))} directed ordered $T graph")
end

Base.show(io::IO, g::OrderedDiGraph) = show(io, MIME"text/plain"(), g)

function Base.:(==)(g::OrderedDiGraph, h::OrderedDiGraph)
    Graphs.nv(g) == Graphs.nv(h) || return false
    Graphs.ne(g) == Graphs.ne(h) || return false
    return g.fadjlist == h.fadjlist && g.badjlist == h.badjlist
end

function Base.copy(g::OrderedDiGraph{T}) where {T}
    # NTuples are immutable — share them; only Vector/Set entries need copying.
    fadj = Union{NTuple{2, T}, Vector{T}}[
        entry isa Vector{T} ? copy(entry) : entry for entry in g.fadjlist
    ]
    badj = Union{NTuple{2, T}, Set{T}}[
        entry isa Set{T} ? copy(entry) : entry for entry in g.badjlist
    ]
    return OrderedDiGraph{T}(g.ne, fadj, badj)
end

#
# Mutation
#

function Graphs.add_vertex!(g::OrderedDiGraph{T}) where {T}
    (Graphs.nv(g) + one(T) <= Graphs.nv(g)) && return false  # overflow guard
    push!(g.fadjlist, (zero(T), zero(T)))
    push!(g.badjlist, (zero(T), zero(T)))
    return true
end

function Graphs.add_edge!(g::OrderedDiGraph{T}, e::Graphs.Edge{T}) where {T}
    s, d = Graphs.src(e), Graphs.dst(e)
    verts = Graphs.vertices(g)
    (s in verts && d in verts) || return false

    @inbounds entry = g.fadjlist[s]
    @inbounds bentry = g.badjlist[d]
    # Parallel edge guard. This checks `bentry` since it is a `Set`.
    _fin(bentry, s) && return false  # parallel edge guard

    if entry isa Vector{T}
        push!(entry, d)
    else
        a, b = entry
        if iszero(a)
            @inbounds g.fadjlist[s] = (d, zero(T))
        elseif iszero(b)
            @inbounds g.fadjlist[s] = (a, d)
        else
            @inbounds g.fadjlist[s] = T[a, b, d]
        end
    end

    g.ne += 1
    if bentry isa Set{T}
        push!(bentry, s)
    else
        a, b = bentry
        if iszero(a)
            @inbounds g.badjlist[d] = (s, zero(T))
        elseif iszero(b)
            @inbounds g.badjlist[d] = (a, s)
        else
            @inbounds g.badjlist[d] = Set{T}((a, b, s))
        end
    end
    return true
end

function Graphs.add_edge!(g::OrderedDiGraph{T}, s::Integer, d::Integer) where {T}
    return Graphs.add_edge!(g, Graphs.Edge{T}(T(s), T(d)))
end

function Graphs.add_edge!(g::OrderedDiGraph{T}, e::Graphs.AbstractEdge) where {T}
    return Graphs.add_edge!(g, T(Graphs.src(e)), T(Graphs.dst(e)))
end

function Graphs.rem_edge!(g::OrderedDiGraph{T}, e::Graphs.Edge{T}) where {T}
    s, d = Graphs.src(e), Graphs.dst(e)
    verts = Graphs.vertices(g)
    (s in verts && d in verts) || return false

    @inbounds entry = g.fadjlist[s]
    if entry isa Vector{T}
        idx = findfirst(==(d), entry)
        idx === nothing && return false
        deleteat!(entry, idx)
    else
        a, b = entry
        if iszero(a)
            return false
        elseif iszero(b)
            a == d || return false
            @inbounds g.fadjlist[s] = (zero(T), zero(T))
        else
            if a == d
                @inbounds g.fadjlist[s] = (b, zero(T))
            elseif b == d
                @inbounds g.fadjlist[s] = (a, zero(T))
            else
                return false
            end
        end
    end

    g.ne -= 1
    @inbounds bentry = g.badjlist[d]
    if bentry isa Set{T}
        delete!(bentry, s)
    else
        a, b = bentry
        if iszero(b)
            @inbounds g.badjlist[d] = (zero(T), zero(T))
        else
            @inbounds g.badjlist[d] = a == s ? (b, zero(T)) : (a, zero(T))
        end
    end
    return true
end

function Graphs.rem_edge!(g::OrderedDiGraph{T}, s::Integer, d::Integer) where {T}
    return Graphs.rem_edge!(g, Graphs.Edge{T}(T(s), T(d)))
end

function Graphs.rem_edge!(g::OrderedDiGraph{T}, e::Graphs.AbstractEdge) where {T}
    return Graphs.rem_edge!(g, T(Graphs.src(e)), T(Graphs.dst(e)))
end

Graphs.rem_vertex!(g::OrderedDiGraph, v::Integer) =
    error("OrderedDiGraph does not support vertex removal")

Graphs.rem_vertices!(g::OrderedDiGraph, vs::AbstractVector{<:Integer}; kwargs...) =
    error("OrderedDiGraph does not support vertex removal")
