using SymbolicUtils, Test
using SymbolicUtils: Term, Add, Mul, Div, Pow, metadata, BasicSymbolic, Symbolic
import TermInterface

hash2(a) = SymbolicUtils.@manually_scope SymbolicUtils.COMPARE_FULL => true hash(a)
isequal2(a, b) = SymbolicUtils.@manually_scope SymbolicUtils.COMPARE_FULL => true isequal(a, b)

struct Ctx1 end
struct Ctx2 end

@testset "Sym" begin
    x1 = only(@syms x)
    x2 = only(@syms x)
    @test x1.id === x2.id
    x3 = only(@syms x::Float64)
    @test x1.id !== x3.id
    x4 = only(@syms x::Float64)
    @test x1.id !== x4.id
    @test x3.id === x4.id
    x5 = only(@syms x::Int)
    x6 = only(@syms x::Int)
    @test x1.id !== x5.id
    @test x3.id !== x5.id
    @test x5.id === x6.id

    xm1 = setmetadata(x1, Ctx1, "meta_1")
    xm2 = setmetadata(x1, Ctx1, "meta_1")
    @test xm1.id === xm2.id
    xm3 = setmetadata(x1, Ctx2, "meta_2")
    @test xm1.id !== xm3.id
end

@syms a b c

@testset "Term" begin
    t1 = sin(a)
    t2 = sin(a)
    @test t1.id === t2.id
    t3 = Term(identity,[a])
    t4 = Term(identity,[a])
    @test t3.id === t4.id
    t5 = Term{Int}(identity,[a])
    @test t3.id !== t5.id
    tm1 = setmetadata(t1, Ctx1, "meta_1")
    @test t1.id !== tm1.id
end

@testset "Add" begin
    d1 = a + b
    d2 = b + a
    @test d1.id === d2.id
    d3 = b - 2 + a
    d4 = a + b  - 2
    @test d3.id === d4.id
    d5 = Add{Int}(0, Dict(a => 1, b => 1))
    @test d5.id !== d1.id

    dm1 = setmetadata(d1,Ctx1,"meta_1")
    @test d1.id !== dm1.id
end

@testset "Mul" begin
    m1 = a*b
    m2 = b*a
    @test m1.id === m2.id
    m3 = 6*a*b
    m4 = 3*a*2*b
    @test m3.id === m4.id
    m5 = Mul{Int}(1, Dict(a => 1, b => 1))
    @test m5.id !== m1.id

    mm1 = setmetadata(m1, Ctx1, "meta_1")
    @test m1.id !== mm1.id
end

@testset "Div" begin
    v1 = a/b
    v2 = a/b
    @test v1.id === v2.id
    v3 = -1/a
    v4 = -1/a
    @test v3.id === v4.id
    v5 = 3a/6
    v6 = 2a/4
    @test v5.id === v6.id
    v7 = Div{Float64}(-1,a, false)
    @test v7.id !== v3.id

    vm1 = setmetadata(v1,Ctx1, "meta_1")
    @test vm1.id !== v1.id
end

@testset "Pow" begin
    p1 = a^b
    p2 = a^b
    @test p1.id === p2.id
    p3 = a^(2^-b)
    p4 = a^(2^-b)
    @test p3.id === p4.id
    p5 = Pow{Float64}(a,b)
    @test p1.id !== p5.id

    pm1 = setmetadata(p1,Ctx1, "meta_1")
    @test pm1.id !== p1.id
end

@testset "Symbolics in metadata" begin
    @syms a b
    a1 = setmetadata(a, Int, b)
    b1 = setmetadata(b, Int, 3)
    a2 = setmetadata(a, Int, b1)
    @test a1.id !== a2.id
    @test !isequal2(a1, a2)
    @test metadata(metadata(a1)[Int]) === nothing
    @test metadata(metadata(a2)[Int])[Int] == 3
end

@testset "Compare metadata of expression tree" begin
    @syms a b
    aa = setmetadata(a, Int, b)
    @test aa.id !== a.id
    @test isequal(a, aa)
    @test !isequal2(a, aa)
    @test !isequal2(2a, 2aa)
end

@testset "Hashconsing can be toggled" begin
    SymbolicUtils.ENABLE_HASHCONSING[] = false
    @syms a b
    x1 = a + b
    x2 = a + b
    @test x1.id === nothing === x2.id
    SymbolicUtils.ENABLE_HASHCONSING[] = true
end

@testset "`hash2` is cached" begin
    @syms a b f(..)
    for ex in [a + b, a * b, f(a)]
        h = hash2(ex)
        @test h == ex.hash2[]
        ex2 = setmetadata(ex, Int, 3)
        @test ex2.hash2[] != h
    end
end

struct MySymbolic <: Symbolic{Real}
    sym::BasicSymbolic{Real}
end

TermInterface.iscall(x::MySymbolic) = iscall(x.sym)
TermInterface.operation(x::MySymbolic) = operation(x.sym)
TermInterface.arguments(x::MySymbolic) = arguments(x.sym)
SymbolicUtils.metadata(x::MySymbolic) = metadata(x.sym)
Base.isequal(a::MySymbolic, b::MySymbolic) = isequal(a.sym, b.sym)

@testset "`isequal_with_metadata` on custom symbolics" begin
    @syms x::Real
    xx = setmetadata(x, Int, 3)
    @test isequal(x, xx)
    @test !isequal2(x, xx)
    myx = MySymbolic(x)
    myxx = MySymbolic(xx)
    @test isequal(myx, myxx)
    @test !isequal2(myx, myxx)

    ex = 2x
    exx = 2xx
    myex = MySymbolic(ex)
    myexx = MySymbolic(exx)
    @test isequal(ex, exx)
    @test !isequal2(ex, exx)
    @test isequal(myex, myexx)
    @test !isequal2(myex, myexx)

    t = Term{Real}(max, Any[x, myex])
    tt = Term{Real}(max, Any[xx, myexx])
    @test isequal(t, tt)
    @test !isequal2(t, tt)
    myt = MySymbolic(t)
    mytt = MySymbolic(tt)
    @test isequal(myt, mytt)
    @test !isequal2(myt, mytt)
end
