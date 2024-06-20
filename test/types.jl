using SymbolicUtils: BasicSymbolic

@testset "Expronicon generated constructors" begin
    s1 = Sym(:abc)
    s2 = Sym(name = :def)
    name = :ghi
    s3 = Sym(; name)
    bs1 = BasicSymbolic{Float64}(impl = s1)
    impl = s2
    bs2 = BasicSymbolic{Int64}(; impl)
    @testset "Sym" begin
        @test_nowarn Sym(Symbol(""))
        @test s1.name == :abc
        @test typeof(s2.name) == Symbol
        @test typeof(s1) == BasicSymbolicImpl
        @test s2.name == :def
        @test s3.name == :ghi
    end
    @testset "Term" begin
        t1 = Term(sin, [bs1])
        @test t1.f == sin
        @test t1.arguments == [bs1]
        @test typeof(t1.arguments) == Vector{BasicSymbolic}
        @test_throws MethodError Term(sin, [s1])
        @test_throws MethodError Term(sin, [1])
        @test_throws MethodError Term(sin, [2.0])
    end
    @testset "Div" begin
        d1 = Div(num = bs1, den = bs2)
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
        d2 =  Div(; num, den)
        @test d2.num == bs1
        @test d2.den == bs2
        @test_throws MethodError Div(num = s1, den = bs2)
        @test_throws MethodError Div(num = bs1, den = s2)
        @test_throws MethodError Div(num = s1, den = s2)
    end
end
