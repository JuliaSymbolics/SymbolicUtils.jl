using SymbolicUtils: OrderedDiGraph, AdjView, OrderedDiGraphEdgeIter
using Graphs
using Test

# ── helpers ────────────────────────────────────────────────────────────────────

# Build a graph from a list of (src, dst) pairs and return it.
function make_graph(n::Int, edges::Pair{Int,Int}...)
    g = OrderedDiGraph{Int}(n)
    for (s, d) in edges
        add_edge!(g, s, d)
    end
    return g
end

# Helper functions for @inferred tests — must be at module scope so that the
# compiler can fully specialize them.
function _sum_outneighbors(g::OrderedDiGraph{Int}, v::Int)
    s = 0
    for x in outneighbors(g, v)
        s += x
    end
    return s
end

function _sum_inneighbors(g::OrderedDiGraph{Int}, v::Int)
    s = 0
    for x in inneighbors(g, v)
        s += x
    end
    return s
end

function _has_any_outneighbor(g::OrderedDiGraph{Int}, v::Int, target::Int)
    for x in outneighbors(g, v)
        x == target && return true
    end
    return false
end

# ── Construction ───────────────────────────────────────────────────────────────

@testset "Construction" begin
    @testset "empty constructors" begin
        g = OrderedDiGraph{Int}()
        @test nv(g) == 0
        @test ne(g) == 0

        g2 = OrderedDiGraph()
        @test eltype(g2) == Int
        @test nv(g2) == 0

        g3 = OrderedDiGraph(Int32)
        @test eltype(g3) == Int32
        @test nv(g3) == 0
    end

    @testset "n-vertex constructor" begin
        g = OrderedDiGraph{Int}(5)
        @test nv(g) == 5
        @test ne(g) == 0
        @test vertices(g) == 1:5

        # Infer T from argument
        g2 = OrderedDiGraph(Int16(4))
        @test eltype(g2) == Int16
        @test nv(g2) == 4
    end

    @testset "copy constructor" begin
        g = make_graph(3, 1=>2, 1=>3, 2=>3)
        h = OrderedDiGraph(g)
        @test g == h
        # Mutating the copy does not affect the original
        add_edge!(h, 3, 1)
        @test !has_edge(g, 3, 1)
        @test ne(h) == ne(g) + 1
    end

    @testset "type-converting copy constructor" begin
        g = make_graph(3, 1=>2, 2=>3)
        h = OrderedDiGraph{Int32}(g)
        @test eltype(h) == Int32
        @test nv(h) == 3 && ne(h) == 2
        @test has_edge(h, 1, 2) && has_edge(h, 2, 3)
        # Insertion order preserved after type conversion
        @test collect(outneighbors(h, 1)) == Int32[2]
        @test collect(outneighbors(h, 2)) == Int32[3]
    end

    @testset "construct from SimpleDiGraph" begin
        sdg = SimpleDiGraph(3)
        add_edge!(sdg, 1, 2)
        add_edge!(sdg, 2, 3)
        g = OrderedDiGraph(sdg)
        @test nv(g) == 3 && ne(g) == 2
        @test has_edge(g, 1, 2) && has_edge(g, 2, 3)
        @test !has_edge(g, 1, 3)
    end

    @testset "zero" begin
        g = zero(OrderedDiGraph{Int})
        @test nv(g) == 0 && ne(g) == 0

        g2 = make_graph(3, 1=>2)
        @test zero(g2) == zero(OrderedDiGraph{Int})
    end
end

# ── Graphs.jl interface ────────────────────────────────────────────────────────

@testset "Graphs.jl interface" begin
    g = make_graph(4, 1=>2, 1=>3, 2=>4, 3=>4)

    @testset "basic queries" begin
        @test nv(g) == 4
        @test ne(g) == 4
        @test vertices(g) == 1:4
        @test is_directed(g)
        @test is_directed(OrderedDiGraph{Int})
        @test edgetype(g) == Graphs.Edge{Int}
    end

    @testset "has_vertex" begin
        @test has_vertex(g, 1)
        @test has_vertex(g, 4)
        @test !has_vertex(g, 0)
        @test !has_vertex(g, 5)
    end

    @testset "has_edge" begin
        @test has_edge(g, 1, 2)
        @test has_edge(g, 1, 3)
        @test has_edge(g, 2, 4)
        @test has_edge(g, 3, 4)
        @test !has_edge(g, 2, 1)   # directed: reverse absent
        @test !has_edge(g, 1, 4)   # no direct edge
        @test !has_edge(g, 4, 4)   # no self-loop
        # Out-of-bounds vertices
        @test !has_edge(g, 0, 1)
        @test !has_edge(g, 1, 5)
    end

    @testset "outneighbors / inneighbors types" begin
        # both always return AdjView{T}
        @test outneighbors(g, 1) isa AdjView{Int}
        @test inneighbors(g, 4)  isa AdjView{Int}
    end

    @testset "indegree / outdegree" begin
        @test outdegree(g, 1) == 2
        @test outdegree(g, 4) == 0
        @test indegree(g, 4) == 2
        @test indegree(g, 1) == 0
    end
end

# ── Insertion-order invariant ──────────────────────────────────────────────────

@testset "Insertion-order invariant" begin
    @testset "spec example" begin
        # From the docstring: insert 2=>3, 1=>3, 1=>2 in that order
        g = OrderedDiGraph{Int}(3)
        add_edge!(g, 2, 3)
        add_edge!(g, 1, 3)
        add_edge!(g, 1, 2)

        @test collect(outneighbors(g, 1)) == [3, 2]
        @test collect(outneighbors(g, 2)) == [3]
        @test isempty(outneighbors(g, 3))
        @test Set(inneighbors(g, 3)) == Set([2, 1])
        @test Set(inneighbors(g, 2)) == Set([1])
    end

    @testset "order is preserved through other mutations" begin
        g = OrderedDiGraph{Int}(5)
        add_edge!(g, 1, 5)
        add_edge!(g, 1, 3)
        add_edge!(g, 1, 2)
        add_edge!(g, 1, 4)
        @test collect(outneighbors(g, 1)) == [5, 3, 2, 4]

        # Removing a non-1 edge does not disturb order
        rem_edge!(g, 1, 3)
        @test collect(outneighbors(g, 1)) == [5, 2, 4]

        # Adding a new edge appends
        add_edge!(g, 1, 3)
        @test collect(outneighbors(g, 1)) == [5, 2, 4, 3]
    end

    @testset "differs from SimpleDiGraph sorted order" begin
        # SimpleDiGraph would have sorted adjacency [2,3]; we should have [3,2]
        g = OrderedDiGraph{Int}(3)
        add_edge!(g, 1, 3)
        add_edge!(g, 1, 2)
        @test collect(outneighbors(g, 1)) == [3, 2]    # insertion order

        sdg = SimpleDiGraph(3)
        add_edge!(sdg, 1, 3)
        add_edge!(sdg, 1, 2)
        @test outneighbors(sdg, 1) == [2, 3]  # sorted
    end
end

# ── fadjlist representation (NTuple / Vector) ──────────────────────────────────

@testset "fadjlist NTuple/Vector representation" begin
    @testset "0 out-edges → AdjView of length 0" begin
        g = OrderedDiGraph{Int}(1)
        nbrs = outneighbors(g, 1)
        @test nbrs isa AdjView{Int}
        @test length(nbrs) == 0
        @test collect(nbrs) == Int[]
    end

    @testset "1 out-edge → AdjView of length 1" begin
        g = OrderedDiGraph{Int}(2)
        add_edge!(g, 1, 2)
        nbrs = outneighbors(g, 1)
        @test nbrs isa AdjView{Int}
        @test length(nbrs) == 1
        @test collect(nbrs) == [2]
    end

    @testset "2 out-edges → AdjView of length 2" begin
        g = OrderedDiGraph{Int}(3)
        add_edge!(g, 1, 3); add_edge!(g, 1, 2)
        nbrs = outneighbors(g, 1)
        @test nbrs isa AdjView{Int}
        @test length(nbrs) == 2
        @test collect(nbrs) == [3, 2]
    end

    @testset "3rd out-edge triggers transition to Vector" begin
        g = OrderedDiGraph{Int}(4)
        add_edge!(g, 1, 2); add_edge!(g, 1, 3); add_edge!(g, 1, 4)
        @test g.fadjlist[1] isa Vector{Int}  # internal representation
        @test outneighbors(g, 1) isa AdjView{Int}
        @test collect(outneighbors(g, 1)) == [2, 3, 4]
    end

    @testset "no regression back to NTuple after rem_edge! on Vector" begin
        g = OrderedDiGraph{Int}(4)
        add_edge!(g, 1, 2); add_edge!(g, 1, 3); add_edge!(g, 1, 4)
        rem_edge!(g, 1, 4)
        # Vector is never shrunk back to NTuple
        @test g.fadjlist[1] isa Vector{Int}  # internal representation
        @test collect(outneighbors(g, 1)) == [2, 3]
    end

    @testset "rem_edge! on NTuple: 2→1 out-edges" begin
        g = OrderedDiGraph{Int}(3)
        add_edge!(g, 1, 3); add_edge!(g, 1, 2)
        rem_edge!(g, 1, 3)
        nbrs = outneighbors(g, 1)
        @test nbrs isa AdjView{Int}
        @test collect(nbrs) == [2]
    end

    @testset "rem_edge! on NTuple: 1→0 out-edges" begin
        g = OrderedDiGraph{Int}(2)
        add_edge!(g, 1, 2)
        rem_edge!(g, 1, 2)
        nbrs = outneighbors(g, 1)
        @test nbrs isa AdjView{Int}
        @test length(nbrs) == 0
    end

    @testset "AdjView supports in-operator" begin
        g = OrderedDiGraph{Int}(3)
        add_edge!(g, 1, 3); add_edge!(g, 1, 2)
        nbrs = outneighbors(g, 1)
        @test 3 in nbrs
        @test 2 in nbrs
        @test !(1 in nbrs)
    end

end

# ── badjlist representation (NTuple / Set) ────────────────────────────────────

@testset "badjlist NTuple/Set representation" begin
    @testset "0 in-edges → AdjView of length 0" begin
        g = OrderedDiGraph{Int}(1)
        nbrs = inneighbors(g, 1)
        @test nbrs isa AdjView{Int}
        @test length(nbrs) == 0
        @test collect(nbrs) == Int[]
    end

    @testset "1 in-edge → AdjView of length 1" begin
        g = OrderedDiGraph{Int}(2)
        add_edge!(g, 2, 1)
        nbrs = inneighbors(g, 1)
        @test nbrs isa AdjView{Int}
        @test length(nbrs) == 1
        @test 2 in nbrs
    end

    @testset "2 in-edges → AdjView backed by NTuple" begin
        g = OrderedDiGraph{Int}(3)
        add_edge!(g, 2, 1); add_edge!(g, 3, 1)
        nbrs = inneighbors(g, 1)
        @test nbrs isa AdjView{Int}
        @test length(nbrs) == 2
        @test g.badjlist[1] isa NTuple{2, Int}  # internal representation
        @test 2 in nbrs && 3 in nbrs
    end

    @testset "3rd in-edge triggers transition to Set" begin
        g = OrderedDiGraph{Int}(4)
        add_edge!(g, 2, 1); add_edge!(g, 3, 1); add_edge!(g, 4, 1)
        @test g.badjlist[1] isa Set{Int}         # internal representation
        nbrs = inneighbors(g, 1)
        @test nbrs isa AdjView{Int}
        @test length(nbrs) == 3
        @test Set(nbrs) == Set([2, 3, 4])
    end

    @testset "no regression back to NTuple after rem_edge! on Set" begin
        g = OrderedDiGraph{Int}(4)
        add_edge!(g, 2, 1); add_edge!(g, 3, 1); add_edge!(g, 4, 1)
        rem_edge!(g, 4, 1)
        @test g.badjlist[1] isa Set{Int}         # still Set after removal
        @test Set(inneighbors(g, 1)) == Set([2, 3])
    end

    @testset "rem_edge! on NTuple: 2→1 in-edges" begin
        g = OrderedDiGraph{Int}(3)
        add_edge!(g, 2, 1); add_edge!(g, 3, 1)
        rem_edge!(g, 3, 1)
        @test g.badjlist[1] isa NTuple{2, Int}
        nbrs = inneighbors(g, 1)
        @test length(nbrs) == 1
        @test 2 in nbrs
    end

    @testset "rem_edge! on NTuple: 1→0 in-edges" begin
        g = OrderedDiGraph{Int}(2)
        add_edge!(g, 2, 1)
        rem_edge!(g, 2, 1)
        @test g.badjlist[1] isa NTuple{2, Int}
        @test length(inneighbors(g, 1)) == 0
    end

    @testset "AdjView supports in-operator (in-neighbors)" begin
        g = OrderedDiGraph{Int}(3)
        add_edge!(g, 2, 1); add_edge!(g, 3, 1)
        nbrs = inneighbors(g, 1)
        @test 2 in nbrs
        @test 3 in nbrs
        @test !(1 in nbrs)
    end

end

# ── add_vertex! / add_vertices! ────────────────────────────────────────────────

@testset "add_vertex! / add_vertices!" begin
    g = OrderedDiGraph{Int}()

    @test add_vertex!(g)
    @test nv(g) == 1

    @test add_vertex!(g)
    @test nv(g) == 2

    add_edge!(g, 1, 2)
    @test ne(g) == 1

    # add_vertices! returns count added
    n_added = add_vertices!(g, 3)
    @test n_added == 3
    @test nv(g) == 5

    # New vertices have empty adjacency
    @test isempty(outneighbors(g, 5))
    @test isempty(inneighbors(g, 5))

    # UInt8 overflow guard
    g8 = OrderedDiGraph{UInt8}(typemax(UInt8))
    @test !add_vertex!(g8)
    @test nv(g8) == typemax(UInt8)
end

# ── add_edge! ──────────────────────────────────────────────────────────────────

@testset "add_edge!" begin
    @testset "returns true on success, false otherwise" begin
        g = OrderedDiGraph{Int}(3)
        @test add_edge!(g, 1, 2)           == true
        @test add_edge!(g, 1, 2)           == false  # duplicate
        @test add_edge!(g, 0, 1)           == false  # src out of range
        @test add_edge!(g, 1, 4)           == false  # dst out of range
        @test ne(g) == 1
    end

    @testset "via Edge object" begin
        g = OrderedDiGraph{Int}(2)
        @test add_edge!(g, Graphs.Edge(1, 2))
        @test has_edge(g, 1, 2)
        @test ne(g) == 1
    end

    @testset "via AbstractEdge" begin
        g = OrderedDiGraph{Int}(3)
        e = Graphs.Edge{Int32}(1, 3)   # different integer type
        @test add_edge!(g, e)
        @test has_edge(g, 1, 3)
    end

    @testset "self-loops allowed" begin
        g = OrderedDiGraph{Int}(2)
        @test add_edge!(g, 1, 1)
        @test has_edge(g, 1, 1)
        @test 1 in outneighbors(g, 1)
        @test 1 in inneighbors(g, 1)
        # Duplicate self-loop blocked
        @test !add_edge!(g, 1, 1)
    end

    @testset "adjacency state after insertion" begin
        g = OrderedDiGraph{Int}(3)
        add_edge!(g, 1, 2)
        add_edge!(g, 1, 3)
        @test collect(outneighbors(g, 1)) == [2, 3]
        @test 1 in inneighbors(g, 2)
        @test 1 in inneighbors(g, 3)
        @test ne(g) == 2
    end
end

# ── rem_edge! ──────────────────────────────────────────────────────────────────

@testset "rem_edge!" begin
    @testset "returns true on success, false otherwise" begin
        g = make_graph(3, 1=>2, 1=>3)
        @test rem_edge!(g, 1, 2)          == true
        @test rem_edge!(g, 1, 2)          == false  # already gone
        @test rem_edge!(g, 2, 1)          == false  # was never there
        @test rem_edge!(g, 0, 1)          == false  # out of range
        @test rem_edge!(g, 1, 5)          == false  # out of range
        @test ne(g) == 1
    end

    @testset "forward and backward adjacency both updated" begin
        g = make_graph(3, 1=>2, 1=>3, 2=>3)
        rem_edge!(g, 1, 3)
        @test collect(outneighbors(g, 1)) == [2]
        @test !(1 in inneighbors(g, 3))
        @test ne(g) == 2
    end

    @testset "via Edge object" begin
        g = make_graph(2, 1=>2)
        @test rem_edge!(g, Graphs.Edge(1, 2))
        @test !has_edge(g, 1, 2)
    end

    @testset "via AbstractEdge" begin
        g = make_graph(3, 1=>3)
        @test rem_edge!(g, Graphs.Edge{Int32}(1, 3))
        @test !has_edge(g, 1, 3)
    end
end

# ── rem_vertex! / rem_vertices! ───────────────────────────────────────────────

@testset "rem_vertex! and rem_vertices! are unsupported" begin
    g = make_graph(3, 1=>2, 2=>3)
    @test_throws ErrorException rem_vertex!(g, 1)
    @test_throws ErrorException rem_vertex!(g, 3)
    @test_throws ErrorException rem_vertices!(g, [1, 2])
    @test_throws ErrorException rem_vertices!(g, Int[]; keep_order=true)
end

# ── edges iterator ─────────────────────────────────────────────────────────────

@testset "edges iterator" begin
    g = make_graph(3, 1=>3, 1=>2, 2=>3)

    @testset "length" begin
        @test length(edges(g)) == ne(g)
    end

    @testset "eltype" begin
        @test eltype(edges(g)) == Graphs.Edge{Int}
    end

    @testset "contains all edges" begin
        edge_set = Set(edges(g))
        @test Graphs.Edge(1, 3) in edge_set
        @test Graphs.Edge(1, 2) in edge_set
        @test Graphs.Edge(2, 3) in edge_set
        @test length(edge_set) == 3
    end

    @testset "in-operator uses has_edge" begin
        es = edges(g)
        @test Graphs.Edge(1, 3) in es
        @test !(Graphs.Edge(3, 1) in es)
    end

    @testset "empty graph" begin
        g0 = OrderedDiGraph{Int}()
        @test length(edges(g0)) == 0
        @test collect(edges(g0)) == Graphs.Edge{Int}[]
    end

    @testset "single vertex, no edges" begin
        g1 = OrderedDiGraph{Int}(1)
        @test collect(edges(g1)) == Graphs.Edge{Int}[]
    end

    @testset "iteration order follows fadjlist" begin
        # Edges from vertex 1 should appear in insertion order
        g2 = make_graph(4, 1=>4, 1=>2, 1=>3, 2=>4)
        collected = collect(edges(g2))
        from1 = [e for e in collected if src(e) == 1]
        @test dst.(from1) == [4, 2, 3]
    end
end

# ── copy and equality ──────────────────────────────────────────────────────────

@testset "copy and ==" begin
    g = make_graph(3, 1=>2, 2=>3)

    @testset "copy is equal to original" begin
        h = copy(g)
        @test g == h
    end

    @testset "copy is independent" begin
        h = copy(g)
        add_edge!(h, 3, 1)
        @test !has_edge(g, 3, 1)
        @test g != h
    end

    @testset "badjlist independence" begin
        h = copy(g)
        rem_edge!(h, 1, 2)
        @test has_edge(g, 1, 2)
    end

    @testset "inequality on different structure" begin
        g1 = make_graph(3, 1=>2)
        g2 = make_graph(3, 2=>1)
        @test g1 != g2
    end

    @testset "inequality on different vertex count" begin
        g1 = make_graph(3, 1=>2)
        g2 = make_graph(4, 1=>2)
        @test g1 != g2
    end
end

# ── Graphs.jl algorithm compatibility ─────────────────────────────────────────

@testset "Graphs.jl algorithm compatibility" begin
    @testset "topological_sort_by_dfs on DAG" begin
        g = make_graph(4, 1=>2, 1=>3, 2=>4, 3=>4)
        topo = topological_sort_by_dfs(g)
        # In a valid topological order every src comes before its dst
        pos = Dict(v => i for (i, v) in enumerate(topo))
        for e in edges(g)
            @test pos[src(e)] < pos[dst(e)]
        end
    end

    @testset "topological_sort on linear chain" begin
        g = make_graph(5, 1=>2, 2=>3, 3=>4, 4=>5)
        topo = topological_sort_by_dfs(g)
        @test topo == [1, 2, 3, 4, 5]
    end

    @testset "indegree / outdegree" begin
        g = make_graph(4, 1=>2, 1=>3, 2=>4, 3=>4)
        @test indegree(g, 1) == 0
        @test outdegree(g, 1) == 2
        @test indegree(g, 4) == 2
        @test outdegree(g, 4) == 0
    end

    @testset "neighbors / all_neighbors" begin
        g = make_graph(3, 1=>2, 3=>1)
        @test Set(all_neighbors(g, 1)) == Set([2, 3])
    end
end

# ── show ───────────────────────────────────────────────────────────────────────

@testset "show" begin
    g = make_graph(3, 1=>2, 2=>3)
    s = sprint(show, g)
    @test occursin("directed ordered", s)
    @test occursin("3", s)   # nv
    @test occursin("2", s)   # ne
end

# ── Type parameterization ──────────────────────────────────────────────────────

@testset "Int32 and UInt8 vertex types" begin
    g32 = OrderedDiGraph{Int32}(3)
    add_edge!(g32, 1, 2); add_edge!(g32, 1, 3)
    @test collect(outneighbors(g32, 1)) == Int32[2, 3]
    @test inneighbors(g32, 2)  isa AdjView{Int32}
    @test has_edge(g32, 1, 2)

    g8 = OrderedDiGraph{UInt8}(4)
    add_edge!(g8, UInt8(1), UInt8(4))
    @test collect(outneighbors(g8, 1)) == UInt8[4]
    @test UInt8(1) in inneighbors(g8, 4)
end

# ── Internal consistency ───────────────────────────────────────────────────────

@testset "Internal consistency (fadjlist ↔ badjlist)" begin
    function check_consistent(g)
        for v in vertices(g)
            for u in outneighbors(g, v)
                @test v in inneighbors(g, u)
            end
            for u in inneighbors(g, v)
                @test v in outneighbors(g, u)
            end
        end
        # ne matches sum of out-degrees
        @test ne(g) == sum(outdegree(g, v) for v in vertices(g); init=0)
    end

    @testset "after insertions" begin
        g = make_graph(5, 1=>2, 1=>3, 2=>4, 3=>4, 4=>5, 2=>5)
        check_consistent(g)
    end

    @testset "after rem_edge!" begin
        g = make_graph(4, 1=>2, 1=>3, 2=>3, 3=>4)
        rem_edge!(g, 1, 3)
        check_consistent(g)
    end

end

# ── Type stability (@inferred) ─────────────────────────────────────────────────

@testset "Type stability (@inferred)" begin
    # `@inferred` requires typeof(result) === inferred_type, so it is only
    # applicable to operations whose inferred return type is a concrete singleton
    # (not a Union). `iterate` always infers to Union{Nothing, Tuple{...}}, so
    # it is excluded here; JET covers iterate in adjview_jet.jl.

    # ── AdjView primitives ────────────────────────────────────────────────────
    ntup0 = AdjView{Int}((0, 0))
    ntup2 = AdjView{Int}((3, 7))
    vec3  = AdjView{Int}([4, 5, 6])
    set3  = AdjView{Int}(Set([4, 5, 6]))

    # length → Int
    @test @inferred(length(ntup0)) === 0
    @test @inferred(length(ntup2)) === 2
    @test @inferred(length(vec3))  === 3
    @test @inferred(length(set3))  === 3

    # in → Bool
    @test  @inferred(3 in ntup2)
    @test !@inferred(5 in ntup2)
    @test  @inferred(5 in vec3)
    @test  @inferred(5 in set3)
    @test !@inferred(9 in set3)

    # getindex → T (ordered backing only)
    @test @inferred(ntup2[1]) === 3
    @test @inferred(ntup2[2]) === 7
    @test @inferred(vec3[2])  === 5

    # ── AdjView loop helpers ──────────────────────────────────────────────────
    # outneighbors / inneighbors return the single concrete type AdjView{T}.
    # A function accumulating an Int across the loop has a concrete inferred type.

    g = OrderedDiGraph{Int}(5)
    add_edge!(g, 1, 3); add_edge!(g, 1, 4)                      # NTuple out-adj for v=1
    add_edge!(g, 2, 1); add_edge!(g, 3, 1); add_edge!(g, 5, 1)  # Set in-adj for v=1

    @test @inferred(_sum_outneighbors(g, 1)) == 7        # 3 + 4
    @test @inferred(_sum_inneighbors(g, 1))  == 10       # 2 + 3 + 5
    @test @inferred(_has_any_outneighbor(g, 1, 3))

    g2 = make_graph(4, 1=>2, 1=>3, 1=>4)                # Vector out-adj for v=1
    @test @inferred(_sum_outneighbors(g2, 1)) == 9       # 2 + 3 + 4

    # ── Graphs.jl API: basic queries ──────────────────────────────────────────
    @test @inferred(nv(g))           === 5
    @test @inferred(ne(g))           === 5
    @test @inferred(vertices(g))     === Base.OneTo(5)
    @test @inferred(is_directed(g))  === true
    @test @inferred(is_directed(OrderedDiGraph{Int})) === true
    @test @inferred(has_vertex(g, 1)) === true
    @test @inferred(has_vertex(g, 6)) === false
    @test @inferred(has_edge(g, 1, 3)) === true
    @test @inferred(has_edge(g, 1, 2)) === false

    # outneighbors / inneighbors return the single concrete type AdjView{T}
    @test @inferred(outneighbors(g, 1)) isa AdjView{Int}
    @test @inferred(inneighbors(g, 1))  isa AdjView{Int}

    # ── Graphs.jl API: edges iterator ─────────────────────────────────────────
    @test @inferred(edges(g))          isa OrderedDiGraphEdgeIter{Int}
    @test @inferred(length(edges(g)))  === 5
    @test @inferred(Graphs.Edge(1, 3) in edges(g)) === true

    # ── Graphs.jl API: mutation ───────────────────────────────────────────────
    gm = OrderedDiGraph{Int}(4)
    add_edge!(gm, 1, 2)
    @test @inferred(add_vertex!(gm))     === true
    @test @inferred(add_edge!(gm, 2, 3)) === true
    @test @inferred(rem_edge!(gm, 2, 3)) === true

    # ── copy / zero / == ──────────────────────────────────────────────────────
    @test @inferred(copy(g))                   isa OrderedDiGraph{Int}
    @test @inferred(zero(OrderedDiGraph{Int})) isa OrderedDiGraph{Int}
    h = copy(g)
    @test @inferred(g == h) === true
end
