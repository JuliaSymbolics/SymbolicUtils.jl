using SymbolicUtils: OrderedDiGraph
import Graphs

@testset "OrderedDiGraph" begin
    @testset "construction" begin
        g = OrderedDiGraph()
        @test Graphs.nv(g) == 0
        @test Graphs.ne(g) == 0
        @test Graphs.is_directed(g)
        @test isempty(Graphs.vertices(g))
        @test isempty(Graphs.edges(g))
    end

    @testset "add_vertex!" begin
        g = OrderedDiGraph()
        @test Graphs.add_vertex!(g)
        @test Graphs.nv(g) == 1
        @test Graphs.has_vertex(g, 1)
        @test !Graphs.has_vertex(g, 2)
        @test isempty(Graphs.outneighbors(g, 1))

        Graphs.add_vertex!(g)
        @test Graphs.nv(g) == 2
        @test length(g.ordered_outneighbors) == 2
    end

    @testset "add_vertices!" begin
        g = OrderedDiGraph()
        @test Graphs.add_vertices!(g, 4) == 4
        @test Graphs.nv(g) == 4
        @test length(g.ordered_outneighbors) == 4
        for v in 1:4
            @test isempty(Graphs.outneighbors(g, v))
        end
    end

    @testset "add_edge! and outneighbors order" begin
        g = OrderedDiGraph()
        Graphs.add_vertices!(g, 4)

        # Add edges out-of-sorted order: 3, 1, 2
        @test Graphs.add_edge!(g, 4, 3)
        @test Graphs.add_edge!(g, 4, 1)
        @test Graphs.add_edge!(g, 4, 2)

        @test Graphs.ne(g) == 3
        @test Graphs.has_edge(g, 4, 3)
        @test Graphs.has_edge(g, 4, 1)
        @test Graphs.has_edge(g, 4, 2)

        # outneighbors must preserve insertion order, NOT sort
        @test Graphs.outneighbors(g, 4) == [3, 1, 2]

        # Underlying SimpleDiGraph stores sorted (just verify via inneighbors)
        @test issetequal(Graphs.inneighbors(g, 3), [4])
        @test issetequal(Graphs.inneighbors(g, 1), [4])
        @test issetequal(Graphs.inneighbors(g, 2), [4])
    end

    @testset "add_edge! duplicate" begin
        g = OrderedDiGraph()
        Graphs.add_vertices!(g, 2)
        @test Graphs.add_edge!(g, 1, 2)
        # Duplicate add returns false and does not append to ordered list
        @test !Graphs.add_edge!(g, 1, 2)
        @test Graphs.ne(g) == 1
        @test Graphs.outneighbors(g, 1) == [2]
    end

    @testset "inneighbors" begin
        g = OrderedDiGraph()
        Graphs.add_vertices!(g, 3)
        Graphs.add_edge!(g, 2, 1)
        Graphs.add_edge!(g, 3, 1)
        @test issetequal(Graphs.inneighbors(g, 1), [2, 3])
        @test isempty(Graphs.inneighbors(g, 2))
        @test isempty(Graphs.inneighbors(g, 3))
    end

    @testset "rem_edge!" begin
        g = OrderedDiGraph()
        Graphs.add_vertices!(g, 4)
        Graphs.add_edge!(g, 1, 4)
        Graphs.add_edge!(g, 1, 2)
        Graphs.add_edge!(g, 1, 3)

        # Remove the middle edge; order of remaining edges is preserved
        @test Graphs.rem_edge!(g, 1, 2)
        @test Graphs.ne(g) == 2
        @test !Graphs.has_edge(g, 1, 2)
        @test Graphs.outneighbors(g, 1) == [4, 3]

        # Removing a non-existent edge returns false
        @test !Graphs.rem_edge!(g, 1, 2)
        @test Graphs.ne(g) == 2
    end

    @testset "rem_vertex! (last vertex only)" begin
        g = OrderedDiGraph()
        Graphs.add_vertices!(g, 3)
        Graphs.add_edge!(g, 3, 1)
        Graphs.add_edge!(g, 3, 2)

        @test Graphs.rem_vertex!(g, 3)
        @test Graphs.nv(g) == 2
        @test Graphs.ne(g) == 0
        @test length(g.ordered_outneighbors) == 2
        @test !Graphs.has_vertex(g, 3)

        # Attempting to remove a non-last vertex throws
        @test_throws ArgumentError Graphs.rem_vertex!(g, 1)
    end

    @testset "topological_sort_by_dfs" begin
        # Build a simple DAG: 1→2, 1→3, 2→4, 3→4 — topo order must have 4 before 2,3 before 1
        g = OrderedDiGraph()
        Graphs.add_vertices!(g, 4)
        Graphs.add_edge!(g, 1, 2)
        Graphs.add_edge!(g, 1, 3)
        Graphs.add_edge!(g, 2, 4)
        Graphs.add_edge!(g, 3, 4)

        # topological_sort_by_dfs: for edge u→v, u appears before v
        order = Graphs.topological_sort_by_dfs(g)
        @test length(order) == 4
        pos = Dict(v => i for (i, v) in enumerate(order))
        @test pos[1] < pos[2]
        @test pos[1] < pos[3]
        @test pos[2] < pos[4]
        @test pos[3] < pos[4]
    end

    @testset "outneighbors order is independent of vertex indices" begin
        # Edges added with decreasing dst: order [5,3,1] must be preserved
        g = OrderedDiGraph()
        Graphs.add_vertices!(g, 6)
        Graphs.add_edge!(g, 6, 5)
        Graphs.add_edge!(g, 6, 3)
        Graphs.add_edge!(g, 6, 1)
        @test Graphs.outneighbors(g, 6) == [5, 3, 1]

        # Edges added with increasing dst: order [1,3,5] must be preserved
        g2 = OrderedDiGraph()
        Graphs.add_vertices!(g2, 6)
        Graphs.add_edge!(g2, 6, 1)
        Graphs.add_edge!(g2, 6, 3)
        Graphs.add_edge!(g2, 6, 5)
        @test Graphs.outneighbors(g2, 6) == [1, 3, 5]
    end
end
