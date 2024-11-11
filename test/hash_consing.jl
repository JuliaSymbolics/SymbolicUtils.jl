using SymbolicUtils, Test
using SymbolicUtils: Term

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
