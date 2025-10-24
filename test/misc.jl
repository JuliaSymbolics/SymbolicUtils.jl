using Test
using SymbolicUtils
using SymbolicUtils: BasicSymbolic, vartype, shape, onepoly, UnimplementedForVariantError
using SymbolicIndexingInterface
using LinearAlgebra

@testset "vartype function" begin
    @syms x::Real
    @test vartype(x) == SymbolicUtils.SymReal
    @test vartype(BasicSymbolic{SymbolicUtils.SymReal}) == SymbolicUtils.SymReal
end

@testset "onepoly function" begin
    result = onepoly()
    @test result isa SymbolicUtils.PolynomialT
    @test isone(result)
end

@testset "operation()/arguments() error cases" begin
    @syms x::Real

    const_val = SymbolicUtils.Const{SymbolicUtils.SymReal}(5)
    @test_throws ArgumentError SymbolicUtils.TermInterface.operation(const_val)
    @test_throws ArgumentError SymbolicUtils.TermInterface.operation(x)
    @test_throws ArgumentError SymbolicUtils.TermInterface.arguments(const_val)
    @test_throws ArgumentError SymbolicUtils.TermInterface.arguments(x)
end

@testset "SymbolicIndexingInterface functions" begin
    @syms x::Real y::Real

    @syms A[1:3]::Real
    @test symbolic_type(A) == ArraySymbolic()

    @test symbolic_type(BasicSymbolic) == ScalarSymbolic()
    @test symbolic_type(BasicSymbolic{SymbolicUtils.SymReal}) == ScalarSymbolic()

    # Test getname with getindex term
    expr = A[1]
    @test getname(expr) == :A

    # Test getname with symbolic function
    @syms f(t)::Real
    @test getname(f) == :f

    # Test hasname on Sym
    @test hasname(x) == true

    # Test hasname on getindex
    @test hasname(A[1]) == true

    # Test hasname on non-named expression
    @test hasname(x + y) == false
end

@testset "shape for non-symbolic values" begin
    # Test shape on Colon
    @test shape(:) == SymbolicUtils.ShapeVecT((1:0,))

    # Test shape on Number
    @test shape(5) == SymbolicUtils.ShapeVecT()
    @test shape(3.14) == SymbolicUtils.ShapeVecT()

    # Test shape on Array
    arr = [1, 2, 3]
    s = shape(arr)
    @test s == SymbolicUtils.ShapeVecT((1:3,))

    # Test shape on Matrix
    mat = [1 2; 3 4]
    s = shape(mat)
    @test s == SymbolicUtils.ShapeVecT((1:2, 1:2))

    # Test shape on UniformScaling
    @test shape(LinearAlgebra.I) isa SymbolicUtils.Unknown
end

@testset "is* functions on non-BasicSymbolic" begin
    # Test that isconst, issym, etc. return false for non-BasicSymbolic
    @test SymbolicUtils.isconst(5) == false
    @test SymbolicUtils.issym("test") == false
    @test SymbolicUtils.isterm(3.14) == false
end

@testset "isequal with Number/Array/Missing" begin
    @syms x::Real
    # Test isequal with Number
    @test isequal(x, 5) == false
    @test isequal(5, x) == false
    @test isequal(SymbolicUtils.Const{SymReal}(5), 5) == false
    @test isequal(5, SymbolicUtils.Const{SymReal}(5)) == false

    # Test isequal with Array
    @test isequal(x, [1, 2, 3]) == false
    @test isequal([1, 2, 3], x) == false
    @test isequal(SymbolicUtils.Const{SymReal}([1, 2, 3]), [1, 2, 3]) == false
    @test isequal([1, 2, 3], SymbolicUtils.Const{SymReal}([1, 2, 3])) == false

    # Test isequal with Missing
    @test isequal(x, missing) == false
    @test isequal(missing, x) == false
end

@testset "defaultval and one_of_vartype for all vartypes" begin
    # Test defaultval for SafeReal and TreeReal
    @test SymbolicUtils.defaultval(BasicSymbolic{SafeReal}) isa BasicSymbolic{SafeReal}
    @test SymbolicUtils.defaultval(BasicSymbolic{TreeReal}) isa BasicSymbolic{TreeReal}
    @test SymbolicUtils._iszero(SymbolicUtils.defaultval(BasicSymbolic{SafeReal}))
    @test SymbolicUtils._iszero(SymbolicUtils.defaultval(BasicSymbolic{TreeReal}))

    # Test zero_of_vartype for SafeReal and TreeReal
    @test SymbolicUtils.zero_of_vartype(SafeReal) isa BasicSymbolic{SafeReal}
    @test SymbolicUtils.zero_of_vartype(TreeReal) isa BasicSymbolic{TreeReal}
    @test SymbolicUtils._iszero(SymbolicUtils.zero_of_vartype(SafeReal))
    @test SymbolicUtils._iszero(SymbolicUtils.zero_of_vartype(TreeReal))

    # Test one_of_vartype for TreeReal
    @test SymbolicUtils.one_of_vartype(SafeReal) isa BasicSymbolic{SafeReal}
    @test SymbolicUtils.one_of_vartype(TreeReal) isa BasicSymbolic{TreeReal}
    @test SymbolicUtils._isone(SymbolicUtils.one_of_vartype(SafeReal))
    @test SymbolicUtils._isone(SymbolicUtils.one_of_vartype(TreeReal))
end

@testset "get_mul_coefficient" begin
    @syms x::Real y::Real
    # Test get_mul_coefficient with nested multiplication
    expr = 2 * x * y
    coeff = SymbolicUtils.get_mul_coefficient(expr)
    @test coeff == 2

    # Test error for non-multiplication
    @test_throws ArgumentError SymbolicUtils.get_mul_coefficient(x + y)
end

@testset "parse_metadata with iterable" begin
    # Test parse_metadata with key-value pairs
    meta_pairs = [Int => 1, String => "test"]
    result = SymbolicUtils.parse_metadata(meta_pairs)
    @test result isa Base.ImmutableDict

    # Test parse_metadata with nothing
    @test SymbolicUtils.parse_metadata(nothing) === nothing
end

@testset "default_shape for AbstractArray" begin
    # Test default_shape for AbstractArray without N parameter
    @test SymbolicUtils.default_shape(AbstractArray{Int}) isa SymbolicUtils.Unknown
end

@testset "parse_shape with iterable" begin
    # Test parse_shape with iterable
    ranges = [(1:3), (1:4)]
    result = SymbolicUtils.parse_shape(ranges)
    @test result isa SymbolicUtils.ShapeVecT
    @test result == SymbolicUtils.ShapeVecT((1:3, 1:4))
end

@testset "Const construction errors" begin
    @syms x::Real
    # Test error when constructing Const with wrong variant type
    @test_throws ErrorException SymbolicUtils.BSImpl.Const{SafeReal}(x)
end

@testset "ratcoeff function" begin
    @syms x::Real
    # Test ratcoeff with multiplication
    expr = 3 * x
    has_rat, coeff = SymbolicUtils.ratcoeff(expr)
    @test has_rat == true
    @test coeff == 3

    # Test ratcoeff with integer
    has_rat, coeff = SymbolicUtils.ratcoeff(5)
    @test has_rat == true
    @test coeff == 5

    # Test ratcoeff with rational
    has_rat, coeff = SymbolicUtils.ratcoeff(3//2)
    @test has_rat == true
    @test coeff == 3//2

    # Test ratcoeff with non-rational
    has_rat, coeff = SymbolicUtils.ratcoeff(3.5)
    @test has_rat == false
end

@testset "safe_div function" begin
    # Test safe_div with integers
    result = SymbolicUtils.safe_div(6, 3)
    @test result == 2//1

    # Test safe_div with floats
    result = SymbolicUtils.safe_div(6.0, 3.0)
    @test result == 2.0
end

@testset "Division operations" begin
    @syms x::Real y::Real

    # Test basic division (covers lines in division code)
    expr = x / y
    @test expr isa BasicSymbolic
    @test SymbolicUtils.isdiv(expr)

    # Test division by one
    expr3 = x / 1
    @test !SymbolicUtils.isdiv(expr3)
end

@testset "Power operations" begin
    @syms x::Real y::Real

    # Test matrix power
    @syms A[1:2,1:2]::Real
    expr = 3x * A
    expr2 = expr ^ 2
    @test SymbolicUtils.isterm(expr2)
    @test operation(expr2) === (*)
    args = arguments(expr2)
    @test isequal(args[1], (3x) ^ 2)
    @test isequal(args[2], A ^ 2)
end

@testset "Array operations with symbolics" begin
    @syms x::Real y::Real

    # Test array of symbolics
    arr = [x, y, x+y]
    const_arr = SymbolicUtils.Const{SymbolicUtils.SymReal}(arr)
    @test operation(const_arr) === SymbolicUtils.array_literal
    args = arguments(const_arr)
    @test unwrap_const(args[1]) == (3,)
    @test length(args) == 4

    # Test tuple of symbolics
    tup = (x, y)
    const_tup = SymbolicUtils.Const{SymbolicUtils.SymReal}(tup)
    @test operation(const_tup) === tuple
    @test length(arguments(const_tup)) == 2
end

@testset "WeakRef isequal" begin
    @syms x::Real y::Real
    # Test isequal with WeakRef
    wr = WeakRef(x)
    @test isequal(x, wr) == isequal(x, x)
    @test isequal(wr, x) == isequal(x, x)
end

@testset "parse_dict" begin
    @syms x::Real y::Real
    # Test parse_dict
    dict = Base.ImmutableDict(x => 1, y => 2)
    result = SymbolicUtils.parse_dict(SymbolicUtils.SymReal, dict)
    @test result isa SymbolicUtils.ACDict{SymbolicUtils.SymReal}
    @test isequal(result, dict)
end

@testset "parse_rangedict" begin
    @syms x::Real i::Int
    # Test parse_rangedict
    dict = Base.ImmutableDict(i => 1:5)
    result = SymbolicUtils.parse_rangedict(SymbolicUtils.SymReal, dict)
    @test result isa SymbolicUtils.RangesT{SymbolicUtils.SymReal}
end

@testset "Base.one and Base.zero on Type" begin
    # Test Base.one and Base.zero on Type
    @test Base.one(BasicSymbolic{SymReal}) === SymbolicUtils.one_of_vartype(SymReal)
    @test Base.zero(BasicSymbolic{SymReal}) === SymbolicUtils.zero_of_vartype(SymReal)
end

@testset "Backslash division operator \\" begin
    @syms x::Real
    @test isequal(x \ 2, 2 / x)
end

@testset "Operations with irrational numbers" begin
    @syms x::Real
    # Test operations with AbstractIrrational
    expr = x + π
    idpi = SymbolicUtils.Term{SymReal}(identity, [pi]; type = Real, shape = [])
    @test expr.dict[idpi] == 1

    expr2 = x * π
    @test expr.dict[idpi] == 1
end

@testset "Matrix and array powers" begin
    @syms x::Real
    # Test power with matrix const
    mat = [1 0; 0 1]
    result = mat ^ x
    @test isequal(unwrap_const(result), mat)

    # Test symbolic matrix power
    @syms A[1:2,1:2]::Real
    result2 = A ^ 2
    @test operation(result2) === (^)
end

@testset "Metadata operations" begin
    @syms x::Real
    @test hasmetadata(x, Float64) == false

    # Test setmetadata and getmetadata
    x_with_meta = SymbolicUtils.setmetadata(x, Float64, 1.5)
    @test SymbolicUtils.hasmetadata(x_with_meta, Float64)
    @test SymbolicUtils.getmetadata(x_with_meta, Float64) == 1.5

    # Test getmetadata with default
    @test SymbolicUtils.getmetadata(x, Float64, "default") == "default"
end
