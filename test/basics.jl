using SymbolicUtils: Variable, FnType, Term, symtype
using SymbolicUtils
using Test

@testset "@vars" begin
    let
        @vars a b::Float64 f(::Real) g(p, h(q::Real))::Int

        @test a isa Variable{Number}
        @test a.name === :a

        @test b isa Variable{Float64}
        @test b.name === :b

        @test f isa Variable{FnType{Tuple{Real}, Number}}
        @test f.name === :f

        @test g isa Variable{FnType{Tuple{Number, FnType{Tuple{Real}, Number}}, Int}}
        @test g.name === :g

        @test f(b) isa Term
        @test symtype(f(b)) === Number
        @test_throws ErrorException f(a)

        @test g(b, f) isa Term
        @test_throws ErrorException g(b, a)

        @test symtype(g(b, f)) === Int
    end
end
