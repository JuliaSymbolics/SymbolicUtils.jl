using SymbolicUtils, Test

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
end
