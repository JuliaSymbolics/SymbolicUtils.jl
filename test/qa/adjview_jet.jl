using SymbolicUtils: OrderedDiGraph, AdjView, OrderedDiGraphEdgeIter
using Graphs
using Test
using JET

# Helper: build AdjView variants directly.
const _ntup0 = AdjView{Int}((0, 0))
const _ntup1 = AdjView{Int}((3, 0))
const _ntup2 = AdjView{Int}((3, 7))
const _vec3  = AdjView{Int}([4, 5, 6])
const _set3  = AdjView{Int}(Set([4, 5, 6]))

# ── AdjView iteration type-stability ──────────────────────────────────────────

@testset "JET: AdjView NTuple variant" begin
    @test_opt iterate(_ntup0)
    @test_opt iterate(_ntup1)
    @test_opt iterate(_ntup2)
    @test_opt iterate(_ntup2, 2)
    @test_opt length(_ntup2)
    @test_opt (3 in _ntup2)
end

@testset "JET: AdjView Vector variant" begin
    @test_opt iterate(_vec3)
    @test_opt iterate(_vec3, 2)
    @test_opt length(_vec3)
    @test_opt (5 in _vec3)
end

@testset "JET: AdjView Set variant" begin
    @test_opt iterate(_set3)
    @test_opt length(_set3)
    @test_opt (5 in _set3)
end

# ── Graph operations ───────────────────────────────────────────────────────────

function _sum_outneighbors_jet(g::OrderedDiGraph{Int}, v::Int)
    s = 0
    for x in outneighbors(g, v)
        s += x
    end
    return s
end

function _sum_inneighbors_jet(g::OrderedDiGraph{Int}, v::Int)
    s = 0
    for x in inneighbors(g, v)
        s += x
    end
    return s
end

@testset "JET: loop over outneighbors (NTuple backing)" begin
    g = OrderedDiGraph{Int}(3)
    add_edge!(g, 1, 2); add_edge!(g, 1, 3)
    @test_opt _sum_outneighbors_jet(g, 1)
end

@testset "JET: loop over outneighbors (Vector backing)" begin
    g = OrderedDiGraph{Int}(4)
    add_edge!(g, 1, 2); add_edge!(g, 1, 3); add_edge!(g, 1, 4)
    @test_opt _sum_outneighbors_jet(g, 1)
end

@testset "JET: loop over inneighbors (NTuple backing)" begin
    g = OrderedDiGraph{Int}(3)
    add_edge!(g, 2, 1); add_edge!(g, 3, 1)
    @test_opt _sum_inneighbors_jet(g, 1)
end

@testset "JET: loop over inneighbors (Set backing)" begin
    g = OrderedDiGraph{Int}(4)
    add_edge!(g, 2, 1); add_edge!(g, 3, 1); add_edge!(g, 4, 1)
    @test_opt _sum_inneighbors_jet(g, 1)
end

# ── Graphs.jl API type-stability ───────────────────────────────────────────────

function _edges_sum_jet(g::OrderedDiGraph{Int})
    s = 0
    for e in edges(g)
        s += src(e) + dst(e)
    end
    return s
end

@testset "JET: nv, ne, vertices, is_directed" begin
    g = OrderedDiGraph{Int}(4)
    add_edge!(g, 1, 2); add_edge!(g, 1, 3)
    @test_opt nv(g)
    @test_opt ne(g)
    @test_opt vertices(g)
    @test_opt is_directed(g)
    @test_opt is_directed(OrderedDiGraph{Int})
end

@testset "JET: has_vertex, has_edge" begin
    g = OrderedDiGraph{Int}(4)
    add_edge!(g, 1, 2)
    @test_opt has_vertex(g, 1)
    @test_opt has_edge(g, 1, 2)
    @test_opt has_edge(g, 1, 4)
end

@testset "JET: outneighbors / inneighbors return AdjView{T}" begin
    g = OrderedDiGraph{Int}(4)
    add_edge!(g, 1, 2); add_edge!(g, 1, 3)
    add_edge!(g, 2, 1); add_edge!(g, 3, 1); add_edge!(g, 4, 1)
    @test_opt outneighbors(g, 1)
    @test_opt inneighbors(g, 1)
end

@testset "JET: edges iterator" begin
    g = OrderedDiGraph{Int}(4)
    add_edge!(g, 1, 2); add_edge!(g, 1, 3); add_edge!(g, 2, 4)
    @test_opt edges(g)
    @test_opt length(edges(g))
    @test_opt iterate(edges(g))
    @test_opt (Graphs.Edge(1, 2) in edges(g))
    @test_opt _edges_sum_jet(g)
end

@testset "JET: add_vertex!, add_edge!, rem_edge!" begin
    g = OrderedDiGraph{Int}(4)
    @test_opt add_vertex!(g)
    @test_opt add_edge!(g, 1, 3)
    @test_opt rem_edge!(g, 1, 3)
end

@testset "JET: copy, ==, zero" begin
    g = OrderedDiGraph{Int}(3)
    add_edge!(g, 1, 2); add_edge!(g, 2, 3)
    h = copy(g)
    @test_opt copy(g)
    @test_opt (g == h)
    @test_opt zero(OrderedDiGraph{Int})
end
