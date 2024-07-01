using SymbolicUtils: BasicSymbolic, _Sym, _Term, _Const, _Add

@testset "Expronicon generated constructors" begin
    s1 = Sym(:abc)
    s2 = Sym(name = :def)
    name = :ghi
    s3 = Sym(; name)
    bs1 = BasicSymbolic{Float64}(impl = s1)
    impl = s2
    bs2 = BasicSymbolic{Int64}(; impl)
    @testset "Sym" begin
        @test typeof(s1) == BasicSymbolicImpl
        @test_nowarn Sym(Symbol(""))
        @test s1.name == :abc
        @test typeof(s2.name) == Symbol
        @test typeof(s1) == BasicSymbolicImpl
        @test s2.name == :def
        @test s3.name == :ghi
    end
    @testset "Term" begin
        t1 = Term(sin, [bs1])
        @test typeof(t1) == BasicSymbolicImpl
        @test t1.f == sin
        @test t1.arguments == [bs1]
        @test typeof(t1.arguments) == Vector{BasicSymbolic}
        @test_throws MethodError Term(sin, [s1])
        @test_throws MethodError Term(sin, [1])
        @test_throws MethodError Term(sin, [2.0])
    end
    @testset "Div" begin
        d1 = Div(num = bs1, den = bs2)
        @test typeof(d1) == BasicSymbolicImpl
        @test typeof(d1.num) == BasicSymbolic{Float64}
        @test typeof(d1.den) == BasicSymbolic{Int64}
        @test d1.num == bs1
        @test d1.den == bs2
        @test typeof(d1.simplified) == Base.RefValue{Bool}
        @test isassigned(d1.simplified)
        @test !d1.simplified[]
        @test typeof(d1.arguments) == Vector{BasicSymbolic}
        @test d1.arguments == [bs1, bs2]
        num = bs1
        den = bs2
        d2 = Div(; num, den)
        @test d2.num == bs1
        @test d2.den == bs2
        @test_throws MethodError Div(num = s1, den = bs2)
        @test_throws MethodError Div(num = bs1, den = s2)
        @test_throws MethodError Div(num = s1, den = s2)
    end
    @testset "Pow" begin
        p1 = Pow(base = bs1, exp = bs2)
        @test typeof(p1) == BasicSymbolicImpl
        @test typeof(p1.base) == BasicSymbolic{Float64}
        @test typeof(p1.exp) == BasicSymbolic{Int64}
        @test p1.base == bs1
        @test p1.exp == bs2
        @test typeof(p1.arguments) == Vector{BasicSymbolic}
        @test p1.arguments == [bs1, bs2]
        base = bs1
        exp = bs2
        p2 = Pow(; base, exp)
        @test p2.base == bs1
        @test p2.exp == bs2
        @test_throws MethodError Pow(base = s1, exp = bs2)
        @test_throws MethodError Pow(base = bs1, exp = s2)
        @test_throws MethodError Pow(base = s1, exp = s2)
    end
    c1 = Const(1)
    bc1 = BasicSymbolic{Int}(impl = c1)
    c2 = Const(val = 3.14)
    bc2 = BasicSymbolic{Float64}(impl = c2)
    @testset "Const" begin
        @test typeof(c1) == BasicSymbolicImpl
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
    coeff = bc1
    dict = Dict(bs1 => 3, bs2 => 5)
    @testset "Add" begin
        a1 = Add(; coeff, dict)
        @test typeof(a1) == BasicSymbolicImpl
        @test a1.coeff isa BasicSymbolic
        @test isequal(a1.coeff, bc1)
        @test typeof(a1.dict) == Dict{BasicSymbolic, Any}
        @test a1.dict == dict
        @test typeof(a1.arguments) == Vector{BasicSymbolic}
        @test isempty(a1.arguments)
        @test typeof(a1.issorted) == Base.RefValue{Bool}
        @test !a1.issorted[]
    end
    @testset "Mul" begin
        m1 = Mul(; coeff, dict)
        @test typeof(m1) == BasicSymbolicImpl
        @test m1.coeff isa BasicSymbolic
        @test isequal(m1.coeff, bc1)
        @test typeof(m1.dict) == Dict{BasicSymbolic, Any}
        @test m1.dict == dict
        @test typeof(m1.arguments) == Vector{BasicSymbolic}
        @test isempty(m1.arguments)
        @test typeof(m1.issorted) == Base.RefValue{Bool}
        @test !m1.issorted[]
    end
    @testset "BasicSymbolic" begin
        @test typeof(bs1) == BasicSymbolic{Float64}
        @test bs1 isa BasicSymbolic
        @test bs1 isa SymbolicUtils.Symbolic
        @test bs1.metadata isa SymbolicUtils.Metadata
        @test bs1.metadata == SymbolicUtils.NO_METADATA
        @test typeof(bs1.hash) == Base.RefValue{UInt}
        @test bs1.hash[] == SymbolicUtils.EMPTY_HASH
    end
end

@testset "Custom constructors" begin
    @testset "Sym" begin
        s1 = _Sym(Int64, :x)
        s2 = _Sym(Float64, :y)
        @test typeof(s1) == BasicSymbolic{Int64}
        @test s1.metadata == SymbolicUtils.NO_METADATA
        @test s1.hash[] == SymbolicUtils.EMPTY_HASH
        @test s1.impl.name == :x
        @test typeof(s2) == BasicSymbolic{Float64}
        @test s2.metadata == SymbolicUtils.NO_METADATA
        @test s2.hash[] == SymbolicUtils.EMPTY_HASH
        @test s2.impl.name == :y
    end
    @testset "Term" begin
        s1 = _Sym(Float64, :x)
        s2 = _Sym(Float64, :y)
        t = _Term(Float64, mod, [s1, s2])
        @test typeof(t) == BasicSymbolic{Float64}
        @test t.metadata == SymbolicUtils.NO_METADATA
        @test t.hash[] == SymbolicUtils.EMPTY_HASH
        @test t.impl.f == mod
        @test t.impl.arguments == [s1, s2]
    end
    @testset "Const" begin
        c1 = _Const(1.0)
        @test typeof(c1) == BasicSymbolic{Float64}
        @test c1.metadata == SymbolicUtils.NO_METADATA
        @test c1.hash[] == SymbolicUtils.EMPTY_HASH
        @test c1.impl.val == 1.0
        c2 = _Const(big"123456789012345678901234567890")
        @test typeof(c2) == BasicSymbolic{BigInt}
        @test c2.metadata == SymbolicUtils.NO_METADATA
        @test c2.hash[] == SymbolicUtils.EMPTY_HASH
        @test c2.impl.val == big"123456789012345678901234567890"
        c3 = _Const(big"1.23456789012345678901")
        @test typeof(c3) == BasicSymbolic{BigFloat}
        @test c3.metadata == SymbolicUtils.NO_METADATA
        @test c3.hash[] == SymbolicUtils.EMPTY_HASH
        @test c3.impl.val == big"1.23456789012345678901"
    end
end

@testset "BasicSymbolic iszero" begin
    c1 = _Const(0)
    @test SymbolicUtils._iszero(c1)
    c2 = _Const(1)
    @test !SymbolicUtils._iszero(c2)
    c3 = _Const(0.0)
    @test SymbolicUtils._iszero(c3)
    c4 = _Const(0.00000000000000000000000001)
    @test !SymbolicUtils._iszero(c4)
    c5 = _Const(big"326264532521352634435352152")
    @test !SymbolicUtils._iszero(c5)
    c6 = _Const(big"0.314654523452")
    @test !SymbolicUtils._iszero(c6)
    s = _Sym(Real, :y)
    @test !SymbolicUtils._iszero(s)
end
