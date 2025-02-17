using SymbolicUtils, Test
using SymbolicUtils: Term, Add, Mul, Div, Pow, hash2, metadata

struct Ctx1 end
struct Ctx2 end

@testset "Sym" begin
    x1 = only(@syms x)
    x2 = only(@syms x)
    @test x1.expr === x2.expr
    x3 = only(@syms x::Float64)
    @test x1.expr !== x3.expr
    x4 = only(@syms x::Float64)
    @test x1.expr !== x4.expr
    @test x3.expr === x4.expr
    x5 = only(@syms x::Int)
    x6 = only(@syms x::Int)
    @test x1.expr !== x5.expr
    @test x3.expr !== x5.expr
    @test x5.expr === x6.expr

    xm1 = setmetadata(x1, Ctx1, "meta_1")
    xm2 = setmetadata(x1, Ctx1, "meta_1")
    @test xm1.expr === xm2.expr
    xm3 = setmetadata(x1, Ctx2, "meta_2")
    @test xm1.expr === xm3.expr
end

@syms a b c

@testset "Term" begin
    t1 = sin(a)
    t2 = sin(a)
    @test t1.expr === t2.expr
    t3 = Term(identity,[a])
    t4 = Term(identity,[a])
    @test t3.expr === t4.expr
    t5 = Term{Int}(identity,[a])
    @test t3.expr !== t5.expr
    tm1 = setmetadata(t1, Ctx1, "meta_1")
    @test t1.expr === tm1.expr
end

@testset "Add" begin
    d1 = a + b
    d2 = b + a
    @test d1.expr === d2.expr
    d3 = b - 2 + a
    d4 = a + b  - 2
    @test d3.expr === d4.expr
    d5 = Add(Int, 0, Dict(a => 1, b => 1))
    @test d5.expr !== d1.expr

    dm1 = setmetadata(d1,Ctx1,"meta_1")
    @test d1.expr === dm1.expr
end

@testset "Mul" begin
    m1 = a*b
    m2 = b*a
    @test m1.expr === m2.expr
    m3 = 6*a*b
    m4 = 3*a*2*b
    @test m3.expr === m4.expr
    m5 = Mul(Int, 1, Dict(a => 1, b => 1))
    @test m5.expr !== m1.expr

    mm1 = setmetadata(m1, Ctx1, "meta_1")
    @test m1.expr === mm1.expr
end

@testset "Div" begin
    v1 = a/b
    v2 = a/b
    @test v1.expr === v2.expr
    v3 = -1/a
    v4 = -1/a
    @test v3.expr === v4.expr
    v5 = 3a/6
    v6 = 2a/4
    @test v5.expr === v6.expr
    v7 = Div{Float64}(-1,a)
    @test v7.expr !== v3.expr

    vm1 = setmetadata(v1,Ctx1, "meta_1")
    @test vm1.expr === v1.expr
end

@testset "Pow" begin
    p1 = a^b
    p2 = a^b
    @test p1.expr === p2.expr
    p3 = a^(2^-b)
    p4 = a^(2^-b)
    @test p3.expr === p4.expr
    p5 = Pow{Float64}(a,b)
    @test p1.expr !== p5.expr

    pm1 = setmetadata(p1,Ctx1, "meta_1")
    @test pm1.expr === p1.expr
end

@testset "Equivalent numbers" begin
    f = 0.5
    r = 1 // 2
    @test hash(f) == hash(r)
    u0 = zero(UInt)
    @test hash2(f, u0) != hash2(r, u0)
    @test f + a !== r + a
end

@testset "Symbolics in metadata" begin
    @syms a b
    a1 = setmetadata(a, Int, b)
    b1 = setmetadata(b, Int, 3)
    a2 = setmetadata(a, Int, b1)
    @test a1.expr === a2.expr
    @test !SymbolicUtils.isequal_with_metadata(a1, a2)
    @test metadata(metadata(a1)[Int]) === nothing
    @test metadata(metadata(a2)[Int])[Int] == 3
end

@testset "Compare metadata of expression tree" begin
    @syms a b
    aa = setmetadata(a, Int, b)
    @test aa.expr === a.expr
    @test isequal(a, aa)
    @test !SymbolicUtils.isequal_with_metadata(a, aa)
    @test !SymbolicUtils.isequal_with_metadata(2a, 2aa)
end

@testset "Hashconsing can be toggled" begin
    SymbolicUtils.ENABLE_HASHCONSING[] = false
    name = gensym(:x)
    x1 = only(@eval @syms $name)
    x2 = only(@eval @syms $name)
    @test x1 !== x2
    SymbolicUtils.ENABLE_HASHCONSING[] = true
end

@testset "`hash2` is cached" begin
    @syms a b f(..)
    for ex in [a + b, a * b, f(a)]
        h = SymbolicUtils.hash2(ex)
        @test h == ex.hash2[]
        ex2 = setmetadata(ex, Int, 3)
        @test ex2.hash2[] == h
    end
end
