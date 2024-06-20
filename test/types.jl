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
end
