using SymbolicUtils: Symbolic, BasicSymbolic, Sym, Term, Add, Mul, Div, Pow, Const
using SymbolicUtils

s1 = Sym{Float64}(:abc)
s2 = Sym{Int64}(; name = :def)
@testset "Sym" begin
    @test typeof(s1) <: BasicSymbolic
    @test typeof(s1) == BasicSymbolic{Float64}
    @test s1 isa BasicSymbolic
    @test s1 isa SymbolicUtils.Symbolic
    @test s1.metadata isa SymbolicUtils.Metadata
    @test s1.metadata == SymbolicUtils.NO_METADATA
    @test s1.name == :abc
    @test typeof(s2) <: BasicSymbolic
    @test typeof(s2) == BasicSymbolic{Int64}
    @test typeof(s2.name) == Symbol
    @test s2.name == :def
end

@testset "Term" begin
    t1 = Term(sin, [s1])
    @test typeof(t1) <: BasicSymbolic
    @test typeof(t1) == BasicSymbolic{Real}
    @test t1.f == sin
    @test isequal(t1.arguments, [s1])
    @test typeof(t1.arguments) == Vector{Symbolic}
end

c1 = Const(1)
c2 = Const(3.14)
@testset "Const" begin
    @test typeof(c1) <: BasicSymbolic
    @test typeof(c1.val) == Int
    @test c1.val == 1
    @test typeof(c2.val) == Float64
    @test c2.val == 3.14
    c3 = Const(big"123456789012345678901234567890")
    @test typeof(c3.val) == BigInt
    @test c3.val == big"123456789012345678901234567890"
    c4 = Const(big"1.23456789012345678901")
    @test typeof(c4.val) == BigFloat
    @test c4.val == big"1.23456789012345678901"
end

coeff = c1
dict = Dict{BasicSymbolic, Any}(s1 => 3, s2 => 5)
@testset "Add" begin
    a1 = Add{Real}(; coeff=coeff, dict=dict)
    @test typeof(a1) <: BasicSymbolic
    @test a1.coeff isa BasicSymbolic
    @test isequal(a1.coeff, c1)
    @test typeof(a1.dict) == Dict{BasicSymbolic, Any}
    @test a1.dict == dict
    @test typeof(a1.arguments) == Vector{Any}
    @test isempty(a1.arguments)
    @test typeof(a1.issorted) == Base.RefValue{Bool}
    @test !a1.issorted[]
end

@testset "Mul" begin
    m1 = Mul{Real}(; coeff=coeff, dict=dict)
    @test typeof(m1) <: BasicSymbolic
    @test m1.coeff isa BasicSymbolic
    @test isequal(m1.coeff, c1)
    @test typeof(m1.dict) == Dict{BasicSymbolic, Any}
    @test m1.dict == dict
    @test typeof(m1.arguments) == Vector{Any}
    @test isempty(m1.arguments)
    @test typeof(m1.issorted) == Base.RefValue{Bool}
    @test !m1.issorted[]
end

@testset "Div" begin
    d1 = Div(s1, s2)
    @test typeof(d1) <: BasicSymbolic
    @test typeof(d1) == BasicSymbolic{Float64}
    @test isequal(d1.num, s1)
    @test isequal(d1.den, s2)
    @test typeof(d1.simplified) == Bool
    @test !d1.simplified
    @test isequal(arguments(d1), [s1, s2])
    d2 = Div{Real}(; num=s1, den=s2)
    @test isequal(d2.num, s1)
    @test isequal(d2.den, s2)
end

@testset "Pow" begin
    p1 = Pow(s1, s2)
    @test typeof(p1) <: BasicSymbolic
    @test isequal(p1.base, s1)
    @test isequal(p1.exp, s2)
    @test isequal(arguments(p1), [s1, s2])
    p2 = Pow{Real}(; base=s1, exp=s2)
    @test isequal(p2.base, s1)
    @test isequal(p2.exp, s2)
end

@testset "BasicSymbolic iszero" begin
    c1 = Const(0)
    @test SymbolicUtils._iszero(c1)
    c2 = Const(1)
    @test !SymbolicUtils._iszero(c2)
    c3 = Const(0.0)
    @test SymbolicUtils._iszero(c3)
    c4 = Const(0.00000000000000000000000001)
    @test !SymbolicUtils._iszero(c4)
    c5 = Const(big"326264532521352634435352152")
    @test !SymbolicUtils._iszero(c5)
    c6 = Const(big"0.314654523452")
    @test !SymbolicUtils._iszero(c6)
    s = Sym{Real}(:y)
    @test !SymbolicUtils._iszero(s)
end
