using SymbolicUtils: Sym, FnType, Term, Add, Mul, Pow, symtype
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

        # issue #91
        @syms h(a,b,c)
        @test isequal(h(1,2,3), h(1,2,3))
    end
end

@testset "hashing" begin
    @syms a b f(x, y)
    @test hash(a) == hash(a)
    @test hash(a) != hash(b)
    @test hash(a+1) == hash(a+1)
    @test hash(sin(a+1)) == hash(sin(a+1))
    @test hash(f(1,a)) == hash(f(1, a))

    c = a
    g = f
    @syms a f(x, y)
    @test hash(a) == hash(c)
    @test hash(g(a, b)) == hash(f(a,b))
    @test hash(f(a, b)) == hash(f(c,b))
    @test hash(sin(a+1)) == hash(sin(c+1))
end

@testset "Base methods" begin
    @syms w::Complex z::Complex a::Real b::Real x

    @test isequal(w + z, Add(0, Dict(w=>1, z=>1)))
    @test isequal(z + a, Add(0, Dict(z=>1, a=>1)))
    @test isequal(a + b, Add(0, Dict(a=>1, b=>1))) # TODO: make this Real
    @test isequal(a + x, Add(0, Dict(a=>1, x=>1)))
    @test isequal(a + z, Add(0, Dict(a=>1, z=>1)))

    # promote_symtype of identity
    @test isequal(Term(identity, [w]), Term{Complex}(identity, [w]))
    @test isequal(+(w), w)
    @test isequal(+(a), a)

    @test isequal(rem2pi(a, RoundNearest), Term{Real}(rem2pi, [a, RoundNearest]))

    # bool
    for f in [(==), (!=), (<=), (>=), (<), (>)]
        @test isequal(f(a, 0), Term{Bool}(f, [a, 0]))
        @test isequal(f(0, a), Term{Bool}(f, [0, a]))
        @test isequal(f(a, a), Term{Bool}(f, [a, a]))
    end

    @test symtype(cond(true, 4, 5)) == Int
    @test symtype(cond(a < 0, b, w)) == Union{Real, Complex}
    @test_throws MethodError w < 0
    @test isequal(w == 0, Term{Bool}(==, [w, 0]))
end

@testset "err test" begin
    @syms t()
    @test_throws ErrorException t(2)
end

@testset "substitute" begin
    @syms a b
    @test substitute(a, Dict(a=>1)) == 1
    @test isequal(substitute(sin(a+b), Dict(a=>1)), sin(b+1))
    @test substitute(a+b, Dict(a=>1, b=>3)) == 4
    @test substitute(exp(a), Dict(a=>2)) ≈ exp(2)
end

@testset "printing" begin
    @syms a b
    @test repr(a+b) == "a + b"
    @test repr(-a) == "-1a"
    @test repr(-a + 3) == "3 + -1a"
    @test repr(-(a + b)) == "-1a + -1b"
end
