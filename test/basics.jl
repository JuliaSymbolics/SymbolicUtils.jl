using SymbolicUtils: Sym, FnType, Term, symtype, Contextual, EmptyCtx
using SymbolicUtils
using Test

@testset "@syms" begin
    let
        @syms a b::Float64 f(::Real) g(p, h(q::Real))::Int

        @test a isa Sym{Number}
        @test a.name === :a

        @test b isa Sym{Float64}
        @test b.name === :b

        @test f isa Sym{FnType{Tuple{Real}, Number}}
        @test f.name === :f

        @test g isa Sym{FnType{Tuple{Number, FnType{Tuple{Real}, Number}}, Int}}
        @test g.name === :g

        @test f(b) isa Term
        @test symtype(f(b)) === Number
        @test_throws ErrorException f(a)

        @test g(b, f) isa Term
        @test_throws ErrorException g(b, a)

        @test symtype(g(b, f)) === Int
    end
end

@testset "methods test" begin
    @syms w::Complex z::Complex a::Real b::Real x

    @test w + z == Term{Complex}(+, [w, z])
    @test z + a == Term{Number}(+, [z, a])
    @test a + b == Term{Real}(+, [a, b])
    @test a + x == Term{Number}(+, [a, x])
    @test a + z == Term{Number}(+, [a, z])

    # promote_symtype of identity
    @test Term(identity, [w]) == Term{Complex}(identity, [w])
    @test +(w) == w
    @test +(a) == a

    @test rem2pi(a, RoundNearest) == Term{Real}(rem2pi, [a, RoundNearest])
end

@testset "err test" begin
    @syms t()
    @test_throws ErrorException t(2)
end

@testset "Contexts" begin
    @syms a b c

    @test @rule(~x::Contextual((x, ctx) -> ctx==EmptyCtx()) => "yes")(1) == "yes"
    @test @rule(~x::Contextual((x, ctx) -> haskey(ctx, x)) => true)(a, Dict(a=>1))
    @test @rule(~x::Contextual((x, ctx) -> haskey(ctx, x)) => true)(b, Dict(a=>1)) === nothing
    @test_throws UndefVarError @rule(~x => __CTX__)(a, "test")
    @test @rule(~x => @ctx)(a, "test") == "test"
    @test @rule(~x::Contextual((x, ctx) -> haskey(ctx, x)) => (@ctx)[~x])(a, Dict(a=>1)) === 1
    @test @rule(~x::Contextual((x, ctx) -> haskey(ctx, x)) => (@ctx)[~x])(b, Dict(a=>1)) === nothing
end
