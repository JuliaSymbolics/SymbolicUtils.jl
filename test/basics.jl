using SymbolicUtils: Symbolic, Sym, FnType, Term, Add, Mul, Pow, symtype, operation, arguments, issym, isterm, BasicSymbolic, term
using SymbolicUtils
using IfElse: ifelse
using Setfield
using Test, ReferenceTests

include("utils.jl")

@testset "@syms" begin
    let
        @syms a b::Float64 f(::Real) g(p, h(q::Real))::Int 

        @test issym(a) && symtype(a) == Number
        @test a.name === :a

        @test issym(b) && symtype(b) == Float64
        @test nameof(b) === :b

        @test issym(f)
        @test f.name === :f
        @test symtype(f) == FnType{Tuple{Real}, Number, Nothing}

        @test issym(g)
        @test g.name === :g
        @test symtype(g) == FnType{Tuple{Number, FnType{Tuple{Real}, Number, Nothing}}, Int, Nothing}

        @test isterm(f(b))
        @test symtype(f(b)) === Number
        @test_throws ErrorException f(a)

        @test isterm(g(b, f))
        @test_throws ErrorException g(b, a)

        @test symtype(g(b, f)) === Int

        # issue #91
        @syms h(a,b,c)
        @test isequal(h(1,2,3), h(1,2,3))

        @syms (f::typeof(max))(::Real, ::AbstractFloat)::Number a::Real
        @test issym(f)
        @test f.name == :f
        @test symtype(f) == FnType{Tuple{Real, AbstractFloat}, Number, typeof(max)}
        @test isterm(f(a, b))
        @test symtype(f(a, b)) == Number

        @syms g(p, (h::typeof(identity))(q::Real)::Number)::Number
        @test issym(g)
        @test g.name == :g
        @test symtype(g) == FnType{Tuple{Number, FnType{Tuple{Real}, Number, typeof(identity)}}, Number, Nothing}
        @test_throws "not a subtype of" g(a, f)
        @syms (f::typeof(identity))(::Real)::Number
        @test symtype(g(a, f)) == Number
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

    ex = sin(a+1)
    h = hash(ex, UInt(0))
    @test ex.hash[] == h
    ex1 = sin(a+1)
    hash(asin(ex1), UInt(0))
    @test ex1.hash[] == h
end

struct Ctx1 end
struct Ctx2 end

@testset "metadata" begin
    @syms a b c
    for a = [a, sin(a), a+b, a*b, a^3]

        a′ = setmetadata(a, Ctx1, "meta_1")

        @test hasmetadata(a′, Ctx1)
        @test !hasmetadata(a′, Ctx2)

        a′ = setmetadata(a′, Ctx2, "meta_2")

        @test hasmetadata(a′, Ctx1)
        @test hasmetadata(a′, Ctx2)

        @test getmetadata(a′, Ctx1) == "meta_1"
        @test getmetadata(a′, Ctx2) == "meta_2"
    end

    # In substitute #283
    #
    @syms f(t) t
    f = setmetadata(f(t), Ctx1, "yes")
    hasmetadata(f, Ctx1) # true
    newf = substitute(f, Dict(a=>b)) # unrelated substitution
    @test hasmetadata(newf, Ctx1)
    @test getmetadata(newf, Ctx1) == "yes"


    @test isequal(substitute(1+sqrt(a), Dict(a => 2), fold=false),
                  1 + term(sqrt, 2, type=Number))
    @test substitute(1+sqrt(a), Dict(a => 2), fold=true) isa Float64
end

@testset "Base methods" begin
    @syms w::Complex z::Complex a::Real b::Real x

    @test isequal(w + z, Add(Complex, 0, Dict(w=>1, z=>1)))
    @test isequal(z + a, Add(Number, 0, Dict(z=>1, a=>1)))
    @test isequal(a + b, Add(Real, 0, Dict(a=>1, b=>1)))
    @test isequal(a + x, Add(Number, 0, Dict(a=>1, x=>1)))
    @test isequal(a + z, Add(Number, 0, Dict(a=>1, z=>1)))

    foo(w, z, a, b) = 1.0
    SymbolicUtils.promote_symtype(::typeof(foo), args...) = Real
    @test SymbolicUtils._promote_symtype(foo, (w, z, a, b,)) === Real

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

    @test symtype(ifelse(true, 4, 5)) == Int
    @test symtype(ifelse(a < 0, b, w)) == Union{Real, Complex}
    @test SymbolicUtils.promote_symtype(ifelse, Bool, Int, Bool) == Union{Int, Bool}
    @test_throws MethodError w < 0
    @test isequal(w == 0, Term{Bool}(==, [w, 0]))

    @eqtest x // 5 == (1 // 5) * x
    @eqtest (1//2 * x) / 5 == (1 // 10) * x
    @eqtest x // Int16(5) == Rational{Int16}(1, 5) * x
    @eqtest 5 // x == 5 / x
    @eqtest x // a == x / a

    # rename
    @set! x.name = :oof
    @test nameof(x) === :oof
end

@testset "array-like operations" begin
    abstract type SquareDummy end
    Base.:*(a::Symbolic{SquareDummy}, b) = b^2
    @syms s t a::SquareDummy A[1:2, 1:2]

    @test isequal(ndims(A), 2)
    @test_broken isequal(a.*[1 (s+t); t pi], [1 (s+t)^2; t^2 pi^2])
    @test isequal(s.*[1 (s+t); t pi], [s s*(s+t); s*t s*pi])
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

@testset "occursin" begin
    @syms a b c
    @test occursin(a, a + b)
    @test !occursin(sin(a), a + b + c)
    @test occursin(sin(a),  a * b + c + sin(a^2 * sin(a)))
    @test occursin(0.01, 0.01*a)
    @test !occursin(0.01, a * b * c)
end

@testset "printing" begin
    @syms a b c
    @test repr(a+b) == "a + b"
    @test repr(-a) == "-a"
    @test repr(term(-, a; type = Real)) == "-a"
    @test repr(-a + 3) == "3 - a"
    @test repr(-(a + b)) == "-a - b"
    @test repr((2a)^(-2a)) == "(2a)^(-2a)"
    @test repr(1/2a) == "1 / (2a)"
    @test repr(2/(2*a)) == "1 / a"
    @test repr(Term(*, [1, 1])) == "1"
    @test repr(Term(*, [2, 1])) == "2*1"
    @test repr((a + b) - (b + c)) == "a - c"
    @test repr(a + -1*(b + c)) == "a - b - c"
    @test repr(a + -1*b) == "a - b"
    @test repr(-1^a) == "-(1^a)"
    @test repr((-1)^a) == "(-1)^a"
end

@testset "polynomial printing" begin
    @syms a b c x[1:3]
    @test repr(b+a) == "a + b"
    @test repr(b-a) == "-a + b"
    @test repr(2a+1+3a^2) == "1 + 2a + 3(a^2)"
    @test repr(2a+1+3a^2+2b+3b^2+4a*b) == "1 + 2a + 2b + 3(a^2) + 4a*b + 3(b^2)"

    @syms a b[1:3] c d[1:3]
    get(x, i) = term(getindex, x, i, type=Number)
    b1, b3, d1, d2 = get(b,1),get(b,3), get(d,1), get(d,2)
    @test repr(a + b3 + b1 + d2 + c) == "a + b[1] + b[3] + c + d[2]"
    @test repr(expand((c + b3 - d1)^3)) == "b[3]^3 + 3(b[3]^2)*c - 3(b[3]^2)*d[1] + 3b[3]*(c^2) - 6b[3]*c*d[1] + 3b[3]*(d[1]^2) + c^3 - 3(c^2)*d[1] + 3c*(d[1]^2) - (d[1]^3)"
end

@testset "inspect" begin
    @syms x y z
    y = SymbolicUtils.setmetadata(y, Integer, 42) # Set some metadata
    ex = z*(2x + 3y + 1)^2/(z+2x)
    @test_reference "inspect_output/ex.txt" sprint(io->SymbolicUtils.inspect(io, ex))
    @test_reference "inspect_output/ex-md.txt" sprint(io->SymbolicUtils.inspect(io, ex, metadata=true))
    @test_reference "inspect_output/ex-nohint.txt" sprint(io->SymbolicUtils.inspect(io, ex, hint=false))
    @test SymbolicUtils.pluck(ex, 12) == 2
    @test_reference "inspect_output/sub10.txt" sprint(io->SymbolicUtils.inspect(io, SymbolicUtils.pluck(ex, 9)))
    @test_reference "inspect_output/sub14.txt" sprint(io->SymbolicUtils.inspect(io, SymbolicUtils.pluck(ex, 14)))
end

@testset "maketerm" begin
    @syms a b c
    @test isequal(SymbolicUtils.maketerm(typeof(b + c), +, [a,  (b+c)], nothing).dict, Dict(a=>1,b=>1,c=>1))
    @test isequal(SymbolicUtils.maketerm(typeof(b^2), ^, [b^2,  1//2],  nothing), b)

    # test that maketerm doesn't hard-code BasicSymbolic subtype
    # and is consistent with BasicSymbolic arithmetic operations
    @test isequal(SymbolicUtils.maketerm(typeof(a / b), *, [a / b, c],  nothing), (a / b) * c)
    @test isequal(SymbolicUtils.maketerm(typeof(a * b), *, [0, c],  nothing), 0)
    @test isequal(SymbolicUtils.maketerm(typeof(a^b), ^, [a * b, 3],  nothing), (a * b)^3)

    # test that maketerm sets metadata correctly
    metadata = Base.ImmutableDict{DataType, Any}(Ctx1, "meta_1")
    metadata2 = Base.ImmutableDict{DataType, Any}(Ctx2, "meta_2")
    
    d = b * c
    @set! d.metadata = metadata2

    s = SymbolicUtils.maketerm(typeof(a + d), +, [a, d], metadata)
    @test isterm(s)
    @test hasmetadata(s, Ctx1)
    @test getmetadata(s, Ctx1) == "meta_1"

    s = SymbolicUtils.maketerm(typeof(a * d), *, [a, d], metadata)
    @test isterm(s)
    @test hasmetadata(s, Ctx1)
    @test getmetadata(s, Ctx1) == "meta_1"

    s = SymbolicUtils.maketerm(typeof(a^b), ^, [a * b, 3], metadata)
    @test !hasmetadata(s, Ctx1)

    s = SymbolicUtils.maketerm(typeof(a^b), *, [a * b, 3], metadata)
    @test hasmetadata(s, Ctx1)
    @test getmetadata(s, Ctx1) == "meta_1"

    # Correct symtype propagation
    ref_expr = a * b
    @test symtype(ref_expr) == Number
    new_expr = SymbolicUtils.maketerm(typeof(ref_expr), (==), [a, b], nothing)
    @test symtype(new_expr) == Bool

    # Doesn't know return type, promoted symtype is Any
    foo(x,y) = x^2 + x 
    new_expr = SymbolicUtils.maketerm(typeof(ref_expr), foo, [a, b], nothing)
    @test symtype(new_expr) == Number

    # Promoted symtype is a subtype of referred
    @syms x::Int y::Int 
    new_expr = SymbolicUtils.maketerm(typeof(ref_expr), (+), [x, y], nothing)
    @test symtype(new_expr) == Int64

    # Check that the Array type does not get changed to AbstractArray
    new_expr = SymbolicUtils.maketerm(
        SymbolicUtils.BasicSymbolic{Vector{Float64}}, sin, [1.0, 2.0], nothing)
    @test symtype(new_expr) == Vector{Float64}
end

toterm(t) = Term{symtype(t)}(operation(t), arguments(t))

@testset "diffs" begin
    @syms a b c
    @test isequal(toterm(-1c), Term{Number}(*, [-1, c]))
    @test isequal(toterm(-1(a+b)), Term{Number}(+, [-1a, -b]))
    @test isequal(toterm((a + b) - (b + c)), Term{Number}(+, [a, -1c]))
end

@testset "hash" begin
    @syms a b
    @test hash(a + b, UInt(0)) === hash(a + b) === hash(a + b, UInt(0)) # test caching
    @test hash(a + b, UInt(2)) !== hash(a + b)
end

@testset "methoderror" begin
    @syms a::Any b::Any

    @test_throws MethodError a * b
    @test_throws MethodError a + b
end

@testset "canonical form" begin
    @syms a b c
    for x in [a, a*b, a^2, sin(a)]
        @test isequal(x * 1, x)
        @test x * 0 === 0
        @test isequal(x + 0, x)
        @test isequal(x + x, 2x)
        @test isequal(x + 2x, 3x)
        @test x - x === 0
        @test isequal(-x, -1x)
        @test isequal(x^1, x)
        @test isequal((x^-1)*inv(x^-1), 1)
    end
end

@testset "isequal" begin
    @syms a b c
    @test isequal(a + b, a + b + 0.01 - 0.01)
    @test isequal(a + NaN, a + NaN)

    @test !isequal(a, missing)
    @test !isequal(missing, b)

    a1 = setmetadata(a, Ctx1, "meta_1")
    a2 = setmetadata(a, Ctx1, "meta_1")
    a3 = setmetadata(a, Ctx2, "meta_2")
    @test !isequal(a, a1)
    @test isequal(a1, a2)
    @test !isequal(a1, a3)
end

@testset "subtyping" begin
    T = FnType{Tuple{T,S,Int} where {T,S}, Real}
    s = Sym{T}(:t)
    @syms a b c::Int
    @test isequal(arguments(s(a, b, c)), [a, b, c])
end

@testset "div" begin
    @syms x::SafeReal y::Real
    @test issym((2x/2y).num)
    @test (2x/3y).num.coeff == 2
    @test (2x/3y).den.coeff == 3
    @test (2x/-3x).num.coeff == -2
    @test (2x/-3x).den.coeff == 3
    @test (2.5x/3x).num.coeff == 2.5
    @test (2.5x/3x).den.coeff == 3
    @test (x/3x).den.coeff == 3

    @syms x y
    @test issym((2x/2y).num)
    @test (2x/3y).num.coeff == 2
    @test (2x/3y).den.coeff == 3
    @test (2x/-3x) == -2//3
    @test (2.5x/3x).num == 2.5
    @test (2.5x/3x).den == 3
    @test (x/3x) == 1//3
    @test isequal(x / 1, x)
    @test isequal(x / -1, -x)
end

@testset "LiteralReal" begin
    @syms x::LiteralReal y::LiteralReal z::LiteralReal
    @test repr(x+x) == "x + x"
    @test repr(x*x) == "x * x"
    @test repr(x*x + x*x) == "(x * x) + (x * x)"
    for ex in [sin(x), x+x, x*x, x\x, x/x]
        @test typeof(sin(x)) <: BasicSymbolic{LiteralReal}
    end
    @test repr(sin(x) + sin(x)) == "sin(x) + sin(x)"
end

@testset "Adjoint" begin
    @syms x::Real y
    ax = adjoint(x)
    @test isequal(ax, x)
    @test ax === x
    @test isequal(adjoint(y), conj(y)) 
end
