using SymbolicUtils: Sym, FnType, Term, Add, Mul, symtype, operation, arguments, issym, isterm, BasicSymbolic, term, basicsymbolic_to_polyvar, get_mul_coefficient, ACDict, Const, shape, ShapeVecT, ArgsT, isarrayop, query
using SymbolicUtils.Code: toexpr
using SymbolicUtils
using ConstructionBase: setproperties
import MultivariatePolynomials as MP
using Setfield
using Test, ReferenceTests
import LinearAlgebra
using SparseArrays

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

        @syms a[1:2] b[1:2]::String c[1:2, 3:4] e::Vector{Int} g::Matrix{Int} i::Array{Int, 3} k(..)[1:2]::Int
        @test shape(a) == ShapeVecT([1:2])
        @test a.type == Vector{Number}
        @test shape(b) == ShapeVecT([1:2])
        @test b.type == Vector{String}
        @test shape(c) == ShapeVecT([1:2, 3:4])
        @test c.type == Matrix{Number}
        @test shape(e) == SymbolicUtils.Unknown(1)
        @test e.type == Vector{Int}
        @test shape(g) == SymbolicUtils.Unknown(2)
        @test g.type == Matrix{Int}
        @test shape(i) == SymbolicUtils.Unknown(3)
        @test i.type == Array{Int, 3}
        @test shape(k) == ShapeVecT([1:2])
        @test k.type == FnType{Tuple, Vector{Int}, Nothing}
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

    @testset "hash is same with and without hashconsing" begin
        @syms a b
        t1 = Term{SymReal}(+, [a, b])
        t2 = Term{SymReal}(+, [a, b]; unsafe = true)
        @test hash(t1) == hash(t2)
    end
end

struct Ctx1 end
struct Ctx2 end

# needs to be written like this to avoid a segfault on Julia 1.10
@info "Metadata test"
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


@test isequal(substitute(1+sqrt(a), Dict(a => 2), fold=Val(false)),
              1 + term(sqrt, 2, type=Real))
@test unwrap_const(substitute(1+sqrt(a), Dict(a => 2), fold=Val(true))) isa Float64
@info "Metadata test ends"

@testset "Base methods" begin
    @syms w::Complex{Real} z::Complex{Real} a::Real b::Real x
    @test isequal(w + z, Add{SymReal}(0, ACDict{SymReal}(w => 1, z => 1); type = Complex{Real}))
    @test isequal(z + a, Add{SymReal}(0, ACDict{SymReal}(z => 1, a => 1); type = Complex{Real}))
    @test isequal(a + b, Add{SymReal}(0, ACDict{SymReal}(a => 1, b => 1); type = Real))
    @test isequal(a + x, Add{SymReal}(0, ACDict{SymReal}(a => 1, x => 1); type = Number))
    @test isequal(a + z, Add{SymReal}(0, ACDict{SymReal}(a => 1, z => 1); type = Complex{Real}))

    foo(w, z, a, b) = 1.0
    SymbolicUtils.promote_symtype(::typeof(foo), args...) = Real
    @test SymbolicUtils._promote_symtype(foo, (w, z, a, b,)) === Real

    # promote_symtype of identity
    @test isequal(Term{SymReal}(identity, [w]), Term{SymReal}(identity, [w]; type = Complex{Real}))
    @test isequal(+(w), w)
    @test isequal(+(a), a)

    @test isequal(rem2pi(a, RoundNearest), Term{SymReal}(rem2pi, [a, RoundNearest]; type = Real))

    # bool
    for f in [(==), (!=), (<=), (>=), (<), (>)]
        @test isequal(f(a, 0), Term{SymReal}(f, [a, 0]; type = Bool))
        @test isequal(f(0, a), Term{SymReal}(f, [0, a]; type = Bool))
        @test isequal(f(a, a), Term{SymReal}(f, [a, a]; type = Bool))
    end

    @test symtype(ifelse(true, 4, 5)) == Int
    @test symtype(ifelse(a < 0, b, w)) == Complex{Real}
    @test SymbolicUtils.promote_symtype(ifelse, Bool, Int, Bool) == Int
    @test_throws MethodError w < 0
    @test isequal(w == 0, Term{SymReal}(==, [w, 0]; type = Bool))

    @syms x::Integer a::Integer
    @eqtest x // 5 == SymbolicUtils.Div{SymReal}(x, 5, false; type = Real)
    @eqtest (1//2 * x) / 5 == (1 // 10) * x
    @eqtest 5 // x == 5 / x
    @eqtest x // a == x / a

    # rename
    @set! x.name = :oof
    @test nameof(x) === :oof
end

@testset "array arithmetic" begin
    @syms a[1:2] a2[1:2] a3[2:3] b[1:3] c[1:2, 1:2] d::Vector{Number} d2::Vector{Number} e::Matrix{Number} f[1:2, 1:2, 1:2] g[1:3, 1:3] h q[1:2, 1:3] x y z

    @test_throws ErrorException BS[1, 2]
    # getindex
    @test BS{SymReal}[1, 2] isa Vector{BasicSymbolic{SymReal}}
    @test BS[1, a] isa Vector{BasicSymbolic{SymReal}}
    # typed_vcat
    @test BS{SymReal}[1; 2] isa Vector{BasicSymbolic{SymReal}}
    @test BS[1; a] isa Vector{BasicSymbolic{SymReal}}
    # typed_hcat
    @test BS{SymReal}[1 2] isa Matrix{BasicSymbolic{SymReal}}
    @test BS[1 a] isa Matrix{BasicSymbolic{SymReal}}
    # typed_hvcat
    @test BS{SymReal}[1 2; 3 4] isa Matrix{BasicSymbolic{SymReal}}
    @test BS[1 a; 3 4] isa Matrix{BasicSymbolic{SymReal}}
    # typed_hvncat, ::Int
    @test BS{SymReal}[1;; 2] isa Matrix{BasicSymbolic{SymReal}}
    @test BS[1;; a] isa Matrix{BasicSymbolic{SymReal}}
    # typed_hvncat, ::Dims ::Bool
    @test BS{SymReal}[1; 2;; 3; 4] isa Matrix{BasicSymbolic{SymReal}}
    @test BS[1; a;; 3; 4] isa Matrix{BasicSymbolic{SymReal}}
    symvec = BS[h, x]
    symmat = BS[h x; y z]
    @test symvec isa Vector{BasicSymbolic{SymReal}}
    @test symmat isa Matrix{BasicSymbolic{SymReal}}
    var = Const{SymReal}(symvec)
    @test var isa BasicSymbolic{SymReal}
    @test isterm(var)
    @test isequal(arguments(var), Const{SymReal}.([(2,), h, x]))
    @test symtype(var) == Vector{Number}
    @test shape(var) == ShapeVecT((1:2,))
    var = Const{SymReal}(symmat)
    @test var isa BasicSymbolic{SymReal}
    @test isterm(var)
    @test isequal(arguments(var), Const{SymReal}.([(2, 2), h, y, x, z]))
    @test symtype(var) == Matrix{Number}
    @test shape(var) == ShapeVecT((1:2, 1:2))
    csymvec = Const{SymReal}(symvec)
    csymmat = Const{SymReal}(symmat)

    var = a + a2
    @test var.dict == ACDict{SymReal}(a => 1, a2 => 1)
    @test shape(var) == ShapeVecT([1:2])
    @test symtype(var) == Vector{Number}
    var = a + symvec
    @test var.dict == ACDict{SymReal}(a => 1, csymvec => 1)
    @test shape(var) == ShapeVecT([1:2])
    @test symtype(var) == Vector{Number}
    var = a + a3
    @test var.dict == ACDict{SymReal}(a => 1, a3 => 1)
    # result is always 1-indexed
    @test shape(var) == ShapeVecT([1:2])
    @test symtype(var) == Vector{Number}
    var = a + d
    @test var.dict == ACDict{SymReal}(a => 1, d => 1)
    # result retains known shape
    @test shape(var) == ShapeVecT([1:2])
    @test symtype(var) == Vector{Number}
    var = d + d2
    @test var.dict == ACDict{SymReal}(d => 1, d2 => 1)
    @test shape(var) == SymbolicUtils.Unknown(1)
    @test symtype(var) == Vector{Number}

    @test_throws ArgumentError a + b
    @test_throws ArgumentError a3 + b
    @test_throws ArgumentError symvec + b
    @test_throws ArgumentError a + c
    @test_throws ArgumentError a3 + c
    @test_throws ArgumentError symvec + c
    @test_throws ArgumentError a + e
    @test_throws ArgumentError a3 + e
    @test_throws ArgumentError symvec + e

    var = a + a
    @test isequal(arguments(var), ArgsT{SymReal}([Const{SymReal}(2), a]))
    @test var.f === *
    @test shape(var) == ShapeVecT([1:2])
    @test symtype(var) == Vector{Number}

    var = c * a
    @test isequal(arguments(var), ArgsT{SymReal}([c, a]))
    @test var.f === *
    @test shape(var) == ShapeVecT([1:2])
    @test symtype(var) == Vector{Number}

    var = c * symvec
    @test isequal(arguments(var), ArgsT{SymReal}([c, csymvec]))
    @test var.f === *
    @test shape(var) == ShapeVecT([1:2])
    @test symtype(var) == Vector{Number}

    var = symmat * a
    @test isequal(arguments(var), ArgsT{SymReal}([csymmat, a]))
    @test var.f === *
    @test shape(var) == ShapeVecT([1:2])
    @test symtype(var) == Vector{Number}

    var = 2 * c * h * c * im
    @test var.f === *
    @test isequal(arguments(var), ArgsT{SymReal}((2 * h * im, c ^ 2)))
    @test shape(var) == ShapeVecT([1:2, 1:2])
    @test symtype(var) == Matrix{Number}
    var = var * a
    @test var.f === *
    @test isequal(arguments(var), ArgsT{SymReal}((2 * h * im, c^2, a)))
    @test shape(var) == ShapeVecT([1:2])
    @test symtype(var) == Vector{Number}

    var = c * e * c
    @test var.f === *
    @test isequal(arguments(var), ArgsT{SymReal}((c, e, c)))
    @test shape(var) == ShapeVecT([1:2, 1:2])
    @test symtype(var) == Matrix{Number}
    var = c * e
    @test var.f === *
    @test isequal(arguments(var), ArgsT{SymReal}((c, e)))
    @test shape(var) == SymbolicUtils.Unknown(2)
    @test symtype(var) == Matrix{Number}
    var = var * c
    @test var.f === *
    @test isequal(arguments(var), ArgsT{SymReal}((c, e, c)))
    @test shape(var) == SymbolicUtils.Unknown(2)
    @test symtype(var) == Matrix{Number}
    var = var * a
    @test var.f === *
    @test isequal(arguments(var), ArgsT{SymReal}((c, e, c, a)))
    @test shape(var) == SymbolicUtils.Unknown(1)
    @test symtype(var) == Vector{Number}

    var = c * e
    var = var * d
    @test var.f === *
    @test isequal(arguments(var), ArgsT{SymReal}((c, e, d)))
    @test shape(var) == SymbolicUtils.Unknown(1)
    @test symtype(var) == Vector{Number}

    var = e * a
    @test var.f === *
    @test isequal(arguments(var), ArgsT{SymReal}((e, a)))
    @test shape(var) == SymbolicUtils.Unknown(1)
    @test symtype(var) == Vector{Number}

    var = e * d
    @test var.f === *
    @test isequal(arguments(var), ArgsT{SymReal}((e, d)))
    @test shape(var) == SymbolicUtils.Unknown(1)
    @test symtype(var) == Vector{Number}

    var = c * c
    var = var * var
    @test var.f === ^
    @test isequal(var.args, ArgsT{SymReal}((c, Const{SymReal}(4))))
    @test shape(var) == ShapeVecT([1:2, 1:2])
    @test symtype(var) == Matrix{Number}

    @test unwrap_const(1 ^ c) == LinearAlgebra.I(2)
    @test unwrap_const(1 ^ e) == LinearAlgebra.I

    var = 2 ^ c
    @test var.f === ^
    @test isequal(var.args, ArgsT{SymReal}((Const{SymReal}(2), c)))
    @test shape(var) == ShapeVecT([1:2, 1:2])
    @test symtype(var) == Matrix{Number}

    # we can't support this without committing type piracy
    @test_throws MethodError 2 ^ symmat

    var = 2 ^ e
    @test var.f === ^
    @test isequal(var.args, ArgsT{SymReal}((Const{SymReal}(2), e)))
    @test shape(var) == SymbolicUtils.Unknown(2)
    @test symtype(var) == Matrix{Number}

    var = c ^ 2
    @test var.f === ^
    @test isequal(var.args, ArgsT{SymReal}((c, Const{SymReal}(2))))
    @test shape(var) == ShapeVecT([1:2, 1:2])
    @test symtype(var) == Matrix{Number}

    var = symmat ^ 2
    @test var isa Matrix{BasicSymbolic{SymReal}}
    @test size(var) == size(symmat)

    var = e ^ 2
    @test var.f === ^
    @test isequal(var.args, ArgsT{SymReal}((e, Const{SymReal}(2))))
    @test shape(var) == SymbolicUtils.Unknown(2)
    @test symtype(var) == Matrix{Number}

    var = h ^ c
    @test var.f === ^
    @test isequal(var.args, ArgsT{SymReal}((h, c)))
    @test shape(var) == ShapeVecT([1:2, 1:2])
    @test symtype(var) == Matrix{Number}

    var = h ^ symmat
    @test var.f === ^
    @test isequal(var.args, ArgsT{SymReal}((h, csymmat)))
    @test shape(var) == ShapeVecT([1:2, 1:2])
    @test symtype(var) == Matrix{Number}

    var = h ^ e
    @test var.f === ^
    @test isequal(var.args, ArgsT{SymReal}((h, e)))
    @test shape(var) == SymbolicUtils.Unknown(2)
    @test symtype(var) == Matrix{Number}

    var = c ^ h
    @test var.f === ^
    @test isequal(var.args, ArgsT{SymReal}((c, h)))
    @test shape(var) == ShapeVecT([1:2, 1:2])
    @test symtype(var) == Matrix{Number}

    var = symmat ^ h
    @test var.f === ^
    @test isequal(var.args, ArgsT{SymReal}((csymmat, h)))
    @test shape(var) == ShapeVecT([1:2, 1:2])
    @test symtype(var) == Matrix{Number}

    var = e ^ h
    @test var.f === ^
    @test isequal(var.args, ArgsT{SymReal}((e, h)))
    @test shape(var) == SymbolicUtils.Unknown(2)
    @test symtype(var) == Matrix{Number}

    @test_throws ArgumentError c * b
    @test_throws ArgumentError b * c
    @test_throws ArgumentError symmat * b
    @test_throws ArgumentError b * symmat
    @test_throws ArgumentError f * g
    @test_throws ArgumentError f * a
    @test_throws ArgumentError c * a * c
    @test_throws ArgumentError c * a * a
    @test_throws ArgumentError 2 ^ a
    @test_throws ArgumentError 2 ^ f
    @test_throws ArgumentError a ^ 2
    @test_throws ArgumentError f ^ 2
    @test_throws ArgumentError 2 ^ d
    @test_throws ArgumentError d ^ 2
    @test_throws ArgumentError q ^ 2
    @test_throws ArgumentError 2 ^ q

    @syms r[1:2, 1:2]::Real r2::Matrix{Real} i::Int j::Real

    var = r ^ 2
    @test shape(var) == ShapeVecT((1:2, 1:2))
    @test symtype(var) == Matrix{Real}
    var = r ^ i
    @test shape(var) == ShapeVecT((1:2, 1:2))
    @test symtype(var) == Matrix{Real}
    var = r ^ 2.4
    @test shape(var) == ShapeVecT((1:2, 1:2))
    @test symtype(var) == Matrix{Complex{Real}}
    var = r ^ h
    @test shape(var) == ShapeVecT((1:2, 1:2))
    @test symtype(var) == Matrix{Number}
    var = r ^ j
    @test shape(var) == ShapeVecT((1:2, 1:2))
    @test symtype(var) == Matrix{Complex{Real}}

    var = r2 ^ 2
    @test shape(var) == SymbolicUtils.Unknown(2)
    @test symtype(var) == Matrix{Real}
    var = r2 ^ i
    @test shape(var) == SymbolicUtils.Unknown(2)
    @test symtype(var) == Matrix{Real}
    var = r2 ^ 2.4
    @test shape(var) == SymbolicUtils.Unknown(2)
    @test symtype(var) == Matrix{Complex{Real}}
    var = r2 ^ h
    @test shape(var) == SymbolicUtils.Unknown(2)
    @test symtype(var) == Matrix{Number}
    var = r2 ^ j
    @test shape(var) == SymbolicUtils.Unknown(2)
    @test symtype(var) == Matrix{Complex{Real}}

    # FSLASH
    # * / Scalar
    var = a / h
    @test shape(var) == shape(a)
    @test symtype(var) == symtype(a)
    var = symvec / h
    @test shape(var) == shape(symvec)
    @test symtype(var) == symtype(csymvec)
    var = a3 / h
    @test shape(var) == shape(a3)
    @test symtype(var) == symtype(a3)
    var = c / h
    @test shape(var) == shape(c)
    @test symtype(var) == symtype(c)
    var = symmat / h
    @test shape(var) == shape(symmat)
    @test symtype(var) == symtype(csymmat)
    var = d / h
    @test shape(var) == shape(d)
    @test symtype(var) == symtype(d)
    var = f / h
    @test shape(var) == shape(f)
    @test symtype(var) == symtype(f)

    # Scalar / Vector
    var = h / a
    @test shape(var) == ShapeVecT((1:1, 1:2))
    @test symtype(var) == Matrix{Number}
    var = h / symvec
    @test shape(var) == ShapeVecT((1:1, 1:2))
    @test symtype(var) == Matrix{Number}
    var = h / a3
    @test shape(var) == ShapeVecT((1:1, 2:3))
    @test symtype(var) == Matrix{Number}
    var = h / d
    @test shape(var) == SymbolicUtils.Unknown(2)
    @test symtype(var) == Matrix{Number}
    # Scalar / Array
    @test_throws ArgumentError h / c
    @test_throws ArgumentError h / symmat
    @test_throws ArgumentError h / e
    @test_throws ArgumentError h / f

    # Vector / Vector
    var = a / a
    @test shape(var) == ShapeVecT((1:2, 1:2))
    @test symtype(var) == Matrix{Number}
    var = a / symvec
    @test shape(var) == ShapeVecT((1:2, 1:2))
    @test symtype(var) == Matrix{Number}
    var = a / a3
    @test shape(var) == ShapeVecT((1:2, 2:3))
    @test symtype(var) == Matrix{Number}
    var = a3 / a
    @test shape(var) == ShapeVecT((2:3, 1:2))
    @test symtype(var) == Matrix{Number}
    var = a3 / symvec
    @test shape(var) == ShapeVecT((2:3, 1:2))
    @test symtype(var) == Matrix{Number}
    var = a3 / b
    @test shape(var) == ShapeVecT((2:3, 1:3))
    @test symtype(var) == Matrix{Number}
    var = a / d
    @test shape(var) == SymbolicUtils.Unknown(2)
    @test symtype(var) == Matrix{Number}
    var = d / a
    @test shape(var) == SymbolicUtils.Unknown(2)
    @test symtype(var) == Matrix{Number}

    @syms cmat[1:3, 1:1] cmat2::Matrix{Number}
    # Vector / Matrix
    var = a / cmat
    @test shape(var) == ShapeVecT((1:2, 1:3))
    @test symtype(var) == Matrix{Number}
    var = symvec / cmat
    @test shape(var) == ShapeVecT((1:2, 1:3))
    @test symtype(var) == Matrix{Number}
    var = a3 / cmat
    @test shape(var) == ShapeVecT((2:3, 1:3))
    @test symtype(var) == Matrix{Number}
    var = d / cmat
    @test shape(var) == SymbolicUtils.Unknown(2)
    @test symtype(var) == Matrix{Number}
    var = a / cmat2
    @test shape(var) == SymbolicUtils.Unknown(2)
    @test symtype(var) == Matrix{Number}
    var = symvec / cmat2
    @test shape(var) == SymbolicUtils.Unknown(2)
    @test symtype(var) == Matrix{Number}
    var = a3 / cmat2
    @test shape(var) == SymbolicUtils.Unknown(2)
    @test symtype(var) == Matrix{Number}
    var = d / cmat2
    @test shape(var) == SymbolicUtils.Unknown(2)
    @test symtype(var) == Matrix{Number}
    @test_throws ArgumentError a / c
    @test_throws ArgumentError a3 / c
    @test_throws ArgumentError symvec / c
    @test_throws ArgumentError a / symmat

    # Matrix / Vector
    @test_throws ArgumentError c / a
    @test_throws ArgumentError c / a3
    @test_throws ArgumentError e / a
    @test_throws ArgumentError e / a3
    @test_throws ArgumentError c / d
    @test_throws ArgumentError e / d
    @test_throws ArgumentError symmat / a
    @test_throws ArgumentError c / symvec

    # Matrix / Matrix
    var = c / c
    @test shape(var) == ShapeVecT((1:2, 1:2))
    @test symtype(var) == Matrix{Number}
    var = c / symmat
    @test shape(var) == ShapeVecT((1:2, 1:2))
    @test symtype(var) == Matrix{Number}
    var = symmat / c
    @test shape(var) == ShapeVecT((1:2, 1:2))
    @test symtype(var) == Matrix{Number}
    var = g / q
    @test shape(var) == ShapeVecT((1:3, 1:2))
    @test symtype(var) == Matrix{Number}
    var = q / g
    @test shape(var) == ShapeVecT((1:2, 1:3))
    @test symtype(var) == Matrix{Number}
    var = c / e
    @test shape(var) == SymbolicUtils.Unknown(2)
    @test symtype(var) == Matrix{Number}
    var = e / c
    @test shape(var) == SymbolicUtils.Unknown(2)
    @test symtype(var) == Matrix{Number}
    @test_throws ArgumentError c / g
    @test_throws ArgumentError g / c
    @test_throws ArgumentError symmat / g
    @test_throws ArgumentError g / symmat

    # BSLASH
    # Scalar \ *
    var = h \ a
    @test shape(var) == ShapeVecT((1:2,))
    @test symtype(var) == Vector{Number}
    var = h \ symvec
    @test shape(var) == ShapeVecT((1:2,))
    @test symtype(var) == Vector{Number}
    var = h \ a3
    @test shape(var) == ShapeVecT((2:3,))
    @test symtype(var) == Vector{Number}
    var = h \ c
    @test shape(var) == ShapeVecT((1:2, 1:2))
    @test symtype(var) == Matrix{Number}
    var = h \ symmat
    @test shape(var) == ShapeVecT((1:2, 1:2))
    @test symtype(var) == Matrix{Number}
    var = h \ q
    @test shape(var) == ShapeVecT((1:2, 1:3))
    @test symtype(var) == Matrix{Number}
    var = h \ f
    @test shape(var) == ShapeVecT((1:2, 1:2, 1:2))
    @test symtype(var) == Array{Number, 3}
    var = h \ d
    @test shape(var) == SymbolicUtils.Unknown(1)
    @test symtype(var) == Vector{Number}
    var = h \ e
    @test shape(var) == SymbolicUtils.Unknown(2)
    @test symtype(var) == Matrix{Number}

    # Vector \ Scalar
    @test_throws ArgumentError a \ h
    @test_throws ArgumentError symvec \ h
    @test_throws ArgumentError a3 \ h
    @test_throws ArgumentError d \ h

    # Vector \ Vector
    var = a \ a
    @test shape(var) == ShapeVecT()
    @test symtype(var) == Number
    var = a \ symvec
    @test shape(var) == ShapeVecT()
    @test symtype(var) == Number
    var = a \ a3
    @test shape(var) == ShapeVecT()
    @test symtype(var) == Number
    var = a3 \ a
    @test shape(var) == ShapeVecT()
    @test symtype(var) == Number
    var = symvec \ a
    @test shape(var) == ShapeVecT()
    @test symtype(var) == Number
    var = a \ d
    @test shape(var) == ShapeVecT()
    @test symtype(var) == Number
    var = d \ a
    @test shape(var) == ShapeVecT()
    @test symtype(var) == Number
    var = d \ d
    @test shape(var) == ShapeVecT()
    @test symtype(var) == Number
    @test_throws ArgumentError b \ a
    @test_throws ArgumentError a \ b
    @test_throws ArgumentError b \ symvec
    @test_throws ArgumentError symvec \ b

    # Vector \ Matrix
    var = a \ c
    @test shape(var) == ShapeVecT((1:1, 1:2))
    @test symtype(var) == Matrix{Number}
    var = symvec \ c
    @test shape(var) == ShapeVecT((1:1, 1:2))
    @test symtype(var) == Matrix{Number}
    var = a \ symmat
    @test shape(var) == ShapeVecT((1:1, 1:2))
    @test symtype(var) == Matrix{Number}
    var = a3 \ c
    @test shape(var) == ShapeVecT((1:1, 1:2))
    @test symtype(var) == Matrix{Number}
    var = d \ c
    @test shape(var) == ShapeVecT((1:1, 1:2))
    @test symtype(var) == Matrix{Number}
    var = a \ e
    @test shape(var) == SymbolicUtils.Unknown(2)
    @test symtype(var) == Matrix{Number}
    var = d \ e
    @test shape(var) == SymbolicUtils.Unknown(2)
    @test symtype(var) == Matrix{Number}
    @test_throws ArgumentError a \ g
    @test_throws ArgumentError a3 \ g
    @test_throws ArgumentError symvec \ g

    # Matrix \ Scalar
    @test_throws ArgumentError c \ h
    @test_throws ArgumentError e \ h
    @test_throws ArgumentError symmat \ h

    # Matrix \ Vector
    var = c \ a
    @test shape(var) == ShapeVecT((1:2,))
    @test symtype(var) == Vector{Number}
    var = c \ symvec
    @test shape(var) == ShapeVecT((1:2,))
    @test symtype(var) == Vector{Number}
    var = symmat \ a
    @test shape(var) == ShapeVecT((1:2,))
    @test symtype(var) == Vector{Number}
    var = c \ a3
    @test shape(var) == ShapeVecT((1:2,))
    @test symtype(var) == Vector{Number}
    var = c \ d
    @test shape(var) == ShapeVecT((1:2,))
    @test symtype(var) == Vector{Number}
    var = e \ a
    @test shape(var) == SymbolicUtils.Unknown(1)
    @test symtype(var) == Vector{Number}
    var = e \ d
    @test shape(var) == SymbolicUtils.Unknown(1)
    @test symtype(var) == Vector{Number}
    @test_throws ArgumentError c \ b

    # Matrix \ Matrix
    var = c \ c
    @test shape(var) == ShapeVecT((1:2, 1:2))
    @test symtype(var) == Matrix{Number}
    var = c \ symmat
    @test shape(var) == ShapeVecT((1:2, 1:2))
    @test symtype(var) == Matrix{Number}
    var = symmat \ c
    @test shape(var) == ShapeVecT((1:2, 1:2))
    @test symtype(var) == Matrix{Number}
    var = c \ e
    @test shape(var) == SymbolicUtils.Unknown(2)
    @test symtype(var) == Matrix{Number}
    var = e \ c
    @test shape(var) == SymbolicUtils.Unknown(2)
    @test symtype(var) == Matrix{Number}
    var = e \ e
    @test shape(var) == SymbolicUtils.Unknown(2)
    @test symtype(var) == Matrix{Number}
    var = c \ q
    @test shape(var) == ShapeVecT((1:2, 1:3))
    @test symtype(var) == Matrix{Number}
    var = q \ c
    @test shape(var) == ShapeVecT((1:3, 1:2))
    @test symtype(var) == Matrix{Number}
    @test_throws ArgumentError c \ g
    @test_throws ArgumentError g \ c
end

@testset "Symbolic getindex" begin
    @syms a b[1:4] c[1:4, 1:4] e::Vector{Number} f::Matrix{Number}
    @syms ii::Integer i[1:2]::Int32 j[2:3]::Int k::Vector{Int} l[1:2, 1:2]::Int m

    csymvec = Const{SymReal}([a, m, a, m])
    csymmat = Const{SymReal}([a m a m; m a m a; a m a m; m a m a])
    @testset "$x - $(shape(x))" for x in [b, e, csymvec]
        @testset "idx = $idx" for idx in [2, ii]
            var = x[idx]
            @test symtype(var) == Number
            @test shape(var) == ShapeVecT()
        end

        @testset "idx = $idx" for idx in [1:2, 3:4, i, j]
            var = x[idx]
            @test symtype(var) == Vector{Number}
            @test shape(var) == ShapeVecT((1:2,))
        end

        if shape(x) isa SymbolicUtils.Unknown
            @test_throws ArgumentError x[:]
        else
            var = x[:]
            @test symtype(var) == Vector{Number}
            @test shape(var) == ShapeVecT((1:4,))
        end

        if isequal(x, csymvec)
            @test_throws BoundsError x[]
            @test_throws BoundsError x[1, 2]
        else
            @test_throws ArgumentError x[]
            @test_throws ArgumentError x[1, 2]
            @test_throws MethodError x[[1 2; 3 4]]
        end
        @test_throws ArgumentError x[k]
        @test_throws ArgumentError x[l]
        @test_throws ArgumentError x[m]
    end
    @testset "$x - $(shape(x))" for x in [c, f, csymmat]
        scalidxs = [ii, 3]
        @testset "idx = $idx" for idx in Iterators.product(scalidxs, scalidxs)
            var = x[idx...]
            @test symtype(var) == Number
            @test shape(var) == ShapeVecT()
        end
        arridxs = [1:2, 3:4, i, j]
        @testset "idx = $idx" for idx in Iterators.product(arridxs, arridxs)
            var = x[idx...]
            @test symtype(var) == Matrix{Number}
            @test shape(var) == ShapeVecT((1:2, 1:2))
        end

        @testset "idx = $idx" for idx in Iterators.product(scalidxs, arridxs)
            var = x[idx...]
            @test symtype(var) == Vector{Number}
            @test shape(var) == ShapeVecT((1:2,))
        end
        @testset "idx = $idx" for idx in Iterators.product(arridxs, scalidxs)
            var = x[idx...]
            @test symtype(var) == Vector{Number}
            @test shape(var) == ShapeVecT((1:2,))
        end

        if shape(x) isa SymbolicUtils.Unknown
            @test_throws ArgumentError x[:, :]
            @test_throws ArgumentError x[1, :]
            @test_throws ArgumentError x[:, 1]
        else
            var = x[:, :]
            @test symtype(var) == Matrix{Number}
            @test shape(var) == ShapeVecT((1:4, 1:4))
            @testset "idx = ($idx, :)" for idx in scalidxs
                var = x[idx, :]
                @test symtype(var) == Vector{Number}
                @test shape(var) == ShapeVecT((1:4,))
                var = x[:, idx]
                @test symtype(var) == Vector{Number}
                @test shape(var) == ShapeVecT((1:4,))
            end
            @testset "idx = ($idx, :)" for idx in arridxs
                var = x[idx, :]
                @test symtype(var) == Matrix{Number}
                @test shape(var) == ShapeVecT((1:2, 1:4))
                var = x[:, idx]
                @test symtype(var) == Matrix{Number}
                @test shape(var) == ShapeVecT((1:4, 1:2))
            end
        end
        if isequal(x, csymmat)
            @test_throws BoundsError x[]
        else
            @test_throws ArgumentError x[]
            @test_throws MethodError x[[1 2; 3 4], 1]
            @test_throws ArgumentError x[1]
        end
        @test_throws ArgumentError x[k, 1]
        @test_throws ArgumentError x[l, 1]
        @test_throws ArgumentError x[m, 1]
    end
end

@testset "err test" begin
    @syms t()
    @test_throws ErrorException t(2)
end

@testset "substitute" begin
    @syms a b
    @test unwrap_const(substitute(a, Dict(a=>1))) == 1
    @test isequal(substitute(sin(a+b), Dict(a=>1)), sin(b+1))
    @test unwrap_const(substitute(a+b, Dict(a=>1, b=>3))) == 4
    @test unwrap_const(substitute(exp(a), Dict(a=>2); fold = Val(true))) ≈ exp(2)
end

@testset "query" begin
    @syms a b c
    @test query(isequal(a), a + b)
    @test !query(isequal(sin(a)), a + b + c)
    @test query(isequal(sin(a)),  a * b + c + sin(a^2 * sin(a)))
    @test query(isequal(Const{SymReal}(0.01)), 0.01^a)
    @test !query(isequal(Const{SymReal}(0.01)), a * b * c)
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
    @test repr(Term{SymReal}(*, [1, 1])) == "1"
    @test repr(Term{SymReal}(*, [2, 1])) == "2*1"
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
    _get(x, i) = term(getindex, x, i, type=Number)
    b1, b3, d1, d2 = _get(b,1),_get(b,3), _get(d,1), _get(d,2)
    @test repr(a + b3 + b1 + d2 + c) == "a + b[1] + b[3] + c + d[2]"
    @test repr(expand((c + b3 - d1)^3)) == "b[3]^3 + 3(b[3]^2)*c - 3(b[3]^2)*d[1] + 3b[3]*(c^2) - 6b[3]*c*d[1] + 3b[3]*(d[1]^2) + c^3 - 3(c^2)*d[1] + 3c*(d[1]^2) - (d[1]^3)"
    # test negative powers sorting
    @test repr((b3^2)^(-2) + a^(-3) + (c*d1)^(-2)) == "1 / (a^3) + 1 / (b[3]^4) + 1 / ((c^2)*(d[1]^2))"

    # test that the "x^2 + y^-1 + sin(a)^3.5 + 2t + 1//1" expression from Symbolics.jl/build_targets.jl is properly sorted
    @syms x1 y1 a1 t1
    @test repr(x1^2 + y1^-1 + sin(a1)^3.5 + 2t1 + 1//1) == "(1//1) + 2t1 + 1 / y1 + x1^2 + sin(a1)^3.5"
end

@testset "inspect" begin
    @syms x y z
    y = SymbolicUtils.setmetadata(y, Integer, 42) # Set some metadata
    ex = z*(2x + 3y + 1)^2/(z+2x)
    @test_reference "inspect_output/ex.txt" sprint(io->SymbolicUtils.inspect(io, ex))
    @test_reference "inspect_output/ex-md.txt" sprint(io->SymbolicUtils.inspect(io, ex, metadata=true))
    @test_reference "inspect_output/ex-nohint.txt" sprint(io->SymbolicUtils.inspect(io, ex, hint=false))
    @test unwrap_const(SymbolicUtils.pluck(ex, 12)) == 2
    @test_reference "inspect_output/sub10.txt" sprint(io->SymbolicUtils.inspect(io, SymbolicUtils.pluck(ex, 9)))
    @test_reference "inspect_output/sub14.txt" sprint(io->SymbolicUtils.inspect(io, SymbolicUtils.pluck(ex, 14)))
end

@testset "maketerm" begin
    @syms a b c
    t = SymbolicUtils.maketerm(typeof(b + c), +, [a,  (b+c)], nothing)
    @test isequal(t.dict, ACDict{SymReal}(a => 1, b => 1, c => 1))
    @test isequal(SymbolicUtils.maketerm(typeof(b^2), ^, [b^2,  1//2],  nothing), b)

    # test that maketerm doesn't hard-code BasicSymbolic subtype
    # and is consistent with BasicSymbolic arithmetic operations
    @test isequal(SymbolicUtils.maketerm(typeof(a / b), *, [a / b, c],  nothing), (a / b) * c)
    @test isequal(SymbolicUtils.maketerm(typeof(a * b), *, [0, c],  nothing), Const{SymReal}(0))
    @test isequal(SymbolicUtils.maketerm(typeof(a^b), ^, [a * b, 3],  nothing), (a * b)^3)

    # test that maketerm sets metadata correctly
    metadata = Base.ImmutableDict{DataType, Any}(Ctx1, "meta_1")
    metadata2 = Base.ImmutableDict{DataType, Any}(Ctx2, "meta_2")
    
    d = b * c
    @set! d.metadata = metadata2

    s = SymbolicUtils.maketerm(typeof(a + d), +, [a, d], metadata)
    args = arguments(s)
    idx = findfirst(isequal(d), args)
    @test getmetadata(args[idx], Ctx2) == "meta_2"
    @test hasmetadata(s, Ctx1)
    @test getmetadata(s, Ctx1) == "meta_1"

    s = SymbolicUtils.maketerm(typeof(a * d), *, [a, d], metadata)
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
    @test symtype(new_expr) == Any
    new_expr = SymbolicUtils.maketerm(typeof(ref_expr), foo, [a, b], nothing; type = Number)
    @test symtype(new_expr) == Number

    # Promoted symtype is a subtype of referred
    @syms x::Int y::Int 
    new_expr = SymbolicUtils.maketerm(typeof(ref_expr), (+), [x, y], nothing)
    @test symtype(new_expr) == Int64

    # Check that the Array type does not get changed to AbstractArray
    new_expr = SymbolicUtils.maketerm(
        SymbolicUtils.BasicSymbolic{SymReal}, sin, [1.0, 2.0], nothing; type = Vector{Float64})
    @test symtype(new_expr) == Vector{Float64}
end

toterm(t) = Term{vartype(t)}(operation(t), sorted_arguments(t); type = symtype(t))

@testset "diffs" begin
    @syms a b c
    @test isequal(toterm(-1c), Term{SymReal}(*, [-1, c]; type = Number))
    @test isequal(toterm(-1(a+b)), Term{SymReal}(+, [-a, -b]; type = Number))
    @test isequal(toterm((a + b) - (b + c)), Term{SymReal}(+, [a, -c]; type = Number))
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
        @test x * 0 === Const{SymReal}(0)
        @test isequal(x + 0, x)
        @test isequal(x + x, 2x)
        @test isequal(x + 2x, 3x)
        @test unwrap_const(x - x) === 0
        @test isequal(-x, -1x)
        @test isequal(x^1, x)
        @test isequal(unwrap_const((x^-1)*inv(x^-1)), 1)
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
    SymbolicUtils.@manually_scope SymbolicUtils.COMPARE_FULL => true begin
        @test !isequal(a, a1)
        @test isequal(a1, a2)
        @test !isequal(a1, a3)
    end
end

@testset "subtyping" begin
    T = FnType{Tuple{T,S,Int} where {T,S}, Real, Nothing}
    s = Sym{SymReal}(:t; type = T)
    @syms a b c::Int
    @test isequal(arguments(s(a, b, c)), [a, b, c])
end

@testset "div" begin
    @syms x y::Real vartype=SafeReal
    @test issym((2x/2y).num)
    @test get_mul_coefficient((2x/3y).num) == 2
    @test get_mul_coefficient((2x/3y).den) == 3
    @test get_mul_coefficient((2x/-3x).num) == -2
    @test get_mul_coefficient((2x/-3x).den) == 3
    @test get_mul_coefficient((2.5x/3x).num) == 2.5
    @test get_mul_coefficient((2.5x/3x).den) == 3
    @test get_mul_coefficient((x/3x).den) == 3

    @syms x y
    @test issym((2x/2y).num)
    @test get_mul_coefficient((2x/3y).num) == 2
    @test get_mul_coefficient((2x/3y).den) == 3
    @test unwrap_const(2x/-3x) == -2//3
    @test unwrap_const((2.5x/3x)) == 2.5/3
    @test unwrap_const(x/3x) == 1//3
    @test isequal(x / 1, x)
    @test isequal(x / -1, -x)
end

@testset "Issue#717: Power with complex exponent" begin
    @syms x
    t = x ^ im
    @test iscall(t)
    @test operation(t) == (^)
    @test isequal(unwrap_const.(arguments(t)), [x, im])
end

@testset "LiteralReal" begin
    @syms x y z vartype=TreeReal
    @test repr(x+x) == "x + x"
    @test repr(x*x) == "x * x"
    @test repr(x*x + x*x) == "(x * x) + (x * x)"
    for ex in [sin(x), x+x, x*x, x\x, x/x]
        @test typeof(sin(x)) === BasicSymbolic{TreeReal}
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

@testset "`setproperties` clears hash" begin
    @syms a b c
    hash(a)
    hash(b)
    hash(c)
    @test hash(a) != hash(setproperties(a; name = :A))
    function foo end
    function bar end
    var = term(foo, [a, b]; type = Real)
    hash(var)
    @test hash(var) != hash(setproperties(var; f = bar))
    var = a + b
    hash(var)
    @test hash(var) != hash(setproperties(var; dict = ACDict{SymReal}(a => 2, b => 2)))
    @test hash(var) != hash(setproperties(var; coeff = 4))
    var = a * b
    hash(var)
    @test hash(var) != hash(setproperties(var; dict = ACDict{SymReal}(a => 2, b => 2)))
    @test hash(var) != hash(setproperties(var; coeff = 4))
    var = a / b
    hash(var)
    @test hash(var) != hash(setproperties(var; num = c))
end

@testset "`substitute` handles identity of */+" begin
    @syms t x(t) y
    x = setmetadata(x(t), Int, 3)
    ex = x * y
    res = substitute(ex, Dict(y => 1))
    SymbolicUtils.@manually_scope SymbolicUtils.COMPARE_FULL => true begin
        @test isequal(res, x)
    end
    ex = x + y
    res = substitute(ex, Dict(y => 0))
    SymbolicUtils.@manually_scope SymbolicUtils.COMPARE_FULL => true begin
        @test isequal(res, x)
    end
end

@testset "Negative coefficient to fractional power" begin
    @syms a
    @test isequal((-5a)^0.5, sqrt(5) * Term{SymReal}(^, [-a, 0.5]; type = Number, shape = ShapeVecT()))
end

@testset "Equivalent expressions across tasks are equal" begin
    @syms a
    task = Threads.@spawn @syms a
    a2 = only(fetch(task))
    @test isequal(a, a2)
    @test SymbolicUtils.@manually_scope SymbolicUtils.COMPARE_FULL => true begin
        isequal(a, a2)
    end
end

@testset "AddMul coefficients are hashconsed properly" begin
    @syms x
    v1 = 0.5x
    @test isequal(v1.coeff, 0.5)
    v2 = (1//2)x
    @test v2.coeff !== 0.5
    @test v2.coeff === 1//2
end

@testset "`imag(::Real)`" begin
    @syms x::Real
    @test SymbolicUtils._iszero(imag(x))
end

@testset "`StableIndices`" begin
    @syms x[1:3] y[-2:5, 3:7] z[-10:-4, 0:5, 1:2]
    for v in [x, y, z]
        idxs = SymbolicUtils.stable_eachindex(v)
        els = [v[i] for i in idxs]
        truth = vec(collect(v))
        @test isequal(els, truth)
        # Test that `eachindex(::StableIndices)` works as intended
        # Also tests `isequal(::StableIndex)`
        @test isequal(collect(idxs), [idxs[i] for i in eachindex(idxs)])

        for i in 1:length(v)
            @test Tuple(idxs[i]) == Tuple(CartesianIndices(Tuple(shape(v)))[i])
        end
    end
end

@testset "promote_symtype with sparse operations" begin
    S = sprand(5, 5, 0.1)
    @syms z[1:5, 1:5]::Real
    @test SymbolicUtils.promote_symtype(*, typeof(S), symtype(z)) == Matrix{Real}
    @test SymbolicUtils.promote_symtype(+, typeof(S), symtype(z)) == Matrix{Real}
    @test SymbolicUtils.promote_symtype(\, typeof(S), symtype(z)) == Matrix{Real}
    @test SymbolicUtils.promote_symtype(/, typeof(S), symtype(z)) == Matrix{Real}
end

@testset "Symbolic `StableIndex`" begin
    @syms x[1:3] y[-2:5, 3:7] z[-10:-4, 0:5, 1:2]
    @syms i::Int j::Int
    idxs = [i, i + j, i * j]
    for v in [x, y, z]
        idx = SymbolicUtils.StableIndex(idxs[1:ndims(v)])
        el = v[idx]
        truth = v[idxs[1:ndims(v)]...]
        @test isequal(el, truth)
    end
end

@testset "`StableIndex{Int}(::BasicSymbolic)`" begin
    @syms x[1:3, 1:3] y j::Int k::Int

    i = SymbolicUtils.StableIndex{Int}(x[1, 3])
    @test i.idxs == [1, 3]
    @test_throws ArgumentError SymbolicUtils.StableIndex{Int}(y)
    @test_throws TypeError SymbolicUtils.StableIndex{Int}(x[j, k])
end

@testset "`StableIndex{Int}` indexing of `Array`" begin
    i = SymbolicUtils.StableIndex([1, 2])
    arr = rand(3, 3)
    @test arr[i] == arr[1, 2]
    arr[i] = 4.5
    @test arr[1, 2] == 4.5
end

@testset "`LinearAlgebra.cross`" begin
    @syms x[1:3] xx[1:3] y::Vector{Real} z[1:4] w::Matrix{Real}

    @test isequal(LinearAlgebra.cross(x, xx), Const{SymReal}(LinearAlgebra.cross(collect(x), collect(xx))))
    @test isequal(LinearAlgebra.cross(x, y), Const{SymReal}(LinearAlgebra.cross(collect(x), [y[1], y[2], y[3]])))
    @test isequal(LinearAlgebra.cross(x, collect(xx)), Const{SymReal}(LinearAlgebra.cross(collect(x), collect(xx))))
    @test isequal(LinearAlgebra.cross(x, [1,2,3]), Const{SymReal}(LinearAlgebra.cross(collect(x), [1,2,3])))
    @test isequal(LinearAlgebra.cross(xx, x), Const{SymReal}(LinearAlgebra.cross(collect(xx), collect(x))))
    @test isequal(LinearAlgebra.cross(y, x), Const{SymReal}(LinearAlgebra.cross([y[1], y[2], y[3]], collect(x))))
    @test isequal(LinearAlgebra.cross(collect(xx), x), Const{SymReal}(LinearAlgebra.cross(collect(xx), collect(x))))
    @test isequal(LinearAlgebra.cross([1,2,3], x), Const{SymReal}(LinearAlgebra.cross([1,2,3], collect(x))))
    @test_throws "3-vector" LinearAlgebra.cross(x, z)
    @test_throws "3-vector" LinearAlgebra.cross(y, z)
    @test_throws "expects vectors" LinearAlgebra.cross(x, w)
    @test_throws "expects vectors" LinearAlgebra.cross(y, w)
end

@testset "`transpose`" begin
    @syms x[1:3] y[1:3, 1:3]

    var = transpose(x)
    @test operation(var) === transpose
    @test symtype(var) == LinearAlgebra.Adjoint{Number, Vector{Number}}
    @test shape(var) == [1:1, 1:3]

    var = transpose(y)
    @test operation(var) === transpose
    @test symtype(var) == LinearAlgebra.Adjoint{Number, Matrix{Number}}
    @test shape(var) == [1:3, 1:3]
end

@testset "`Const`-ification of `adjoint`/`transpose`" begin
    @syms a b c

    v1 = [a, b, c]
    var = Const{SymReal}(v1')
    @test operation(var) === adjoint
    @test symtype(var) == LinearAlgebra.Adjoint{Number, Vector{Number}}

    @test shape(var) == [1:1, 1:3]
    @test isequal(collect(var), v1')

    v1 = [a b c; b c a; c a b]
    var = Const{SymReal}(v1')
    @test operation(var) === adjoint
    @test symtype(var) == LinearAlgebra.Adjoint{Number, Matrix{Number}}
    @test shape(var) == [1:3, 1:3]
    @test isequal(collect(var), v1')
end

@testset "`^` doesn't distribute into `/`" begin
    @syms a b c
    ex = (a / b) ^ c
    @test operation(ex) === (^)
    @test isequal(arguments(ex), [a/b, c])
end

@testset "Vector * transpose(Vector) works" begin
    @syms b[1:3] c[2:6] d[3:3, -1:4]
    ex = b * c'
    @test symtype(ex) === Matrix{Number}
    @test shape(ex) == [1:3, 2:6]

    ex = b * d
    @test symtype(ex) === Matrix{Number}
    @test shape(ex) == [1:3, -1:4]
end

@testset "Issue#838: Handle `x'x` dot product" begin
    @syms x[1:3] y[1:3, 1:4]
    @test symtype(x') === LinearAlgebra.Adjoint{Number, Vector{Number}}
    @test symtype(x'x) === Number
    @test symtype(x'y) === LinearAlgebra.Adjoint{Number, Matrix{Number}}
end
