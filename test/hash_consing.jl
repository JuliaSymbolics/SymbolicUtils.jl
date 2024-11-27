using SymbolicUtils, Test
using SymbolicUtils: Term, Add, Mul, Div, Pow, hash2

struct Ctx1 end
struct Ctx2 end

@testset "Sym" begin
    x1 = only(@syms x)
    x2 = only(@syms x)
    @test x1 === x2
    x3 = only(@syms x::Float64)
    @test x1 !== x3
    x4 = only(@syms x::Float64)
    @test x1 !== x4
    @test x3 === x4
    x5 = only(@syms x::Int)
    x6 = only(@syms x::Int)
    @test x1 !== x5
    @test x3 !== x5
    @test x5 === x6

    xm1 = setmetadata(x1, Ctx1, "meta_1")
    xm2 = setmetadata(x1, Ctx1, "meta_1")
    @test xm1 === xm2
    xm3 = setmetadata(x1, Ctx2, "meta_2")
    @test xm1 !== xm3
end

@syms a b c

@testset "Term" begin
    t1 = sin(a)
    t2 = sin(a)
    @test t1 === t2
    t3 = Term(identity,[a])
    t4 = Term(identity,[a])
    @test t3 === t4
    t5 = Term{Int}(identity,[a])
    @test t3 !== t5
    tm1 = setmetadata(t1, Ctx1, "meta_1")
    @test t1 !== tm1
end

@testset "Add" begin
    d1 = a + b
    d2 = b + a
    @test d1 === d2
    d3 = b - 2 + a
    d4 = a + b  - 2
    @test d3 === d4
    d5 = Add(Int, 0, Dict(a => 1, b => 1))
    @test d5 !== d1

    dm1 = setmetadata(d1,Ctx1,"meta_1")
    @test d1 !== dm1
end

@testset "Mul" begin
    m1 = a*b
    m2 = b*a
    @test m1 === m2
    m3 = 6*a*b
    m4 = 3*a*2*b
    @test m3 === m4
    m5 = Mul(Int, 1, Dict(a => 1, b => 1))
    @test m5 !== m1

    mm1 = setmetadata(m1, Ctx1, "meta_1")
    @test m1 !== mm1
end

@testset "Div" begin
    v1 = a/b
    v2 = a/b
    @test v1 === v2
    v3 = -1/a
    v4 = -1/a
    @test v3 === v4
    v5 = 3a/6
    v6 = 2a/4
    @test v5 === v6
    v7 = Div{Float64}(-1,a)
    @test v7 !== v3

    vm1 = setmetadata(v1,Ctx1, "meta_1")
    @test vm1 !== v1
end

@testset "Pow" begin
    p1 = a^b
    p2 = a^b
    @test p1 === p2
    p3 = a^(2^-b)
    p4 = a^(2^-b)
    @test p3 === p4
    p5 = Pow{Float64}(a,b)
    @test p1 !== p5

    pm1 = setmetadata(p1,Ctx1, "meta_1")
    @test pm1 !== p1
end

@testset "Equivalent numbers" begin
    f = 0.5
    r = 1 // 2
    @test hash(f) == hash(r)
    @test hash2(f) != hash2(r)
end
