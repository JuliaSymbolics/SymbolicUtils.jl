using SymbolicUtils
using SymbolicUtils: Sym, BasicSymbolic, fraction_iszero, fraction_isone
using TermInterface

# to avoid running into hashconsed variables that have precomputed `arguments` etc
a = Sym{SymReal}(gensym(:a), type = Number)
b = Sym{SymReal}(gensym(:b), type = Number)
c = Sym{SymReal}(gensym(:c), type = Int)
d = Sym{SymReal}(gensym(:d), type = Real)

@testset "Add" begin
    @test_nowarn @inferred a + b
    @test_nowarn @inferred a + c
    @test_nowarn @inferred a + b + c + d
    @test_nowarn @inferred 2 + a + b + c
    @test_nowarn @inferred a + 2 + b + 2 + c
    @test_nowarn @inferred 1 + 2 + 3 + 4 + a + b
    tmp = (a + b)
    @test_nowarn @inferred tmp + c
end

@testset "Sub" begin
    @test_nowarn @inferred a - b
    @test_nowarn @inferred a - 2
    @test_nowarn @inferred 2 - a
    @test_nowarn @inferred -a
end

@testset "Mul" begin
    @test_nowarn @inferred a * b
    @test_nowarn @inferred a * c
    @test_nowarn @inferred a * b * c * d
    @test_nowarn @inferred 2 * a * b * c
    @test_nowarn @inferred a * 2 * b * 2 * c
    @test_nowarn @inferred 1 * 2 * 3 * 4 * a * b
    tmp = (a * b)
    @test_nowarn @inferred tmp * c
    tmp = a^2
    @test_nowarn @inferred tmp * a * b
end

@testset "Div" begin
    @test_nowarn @inferred a / 2
    @test_nowarn @inferred 2 / a
    @test_nowarn @inferred a / b
    @test_nowarn @inferred a / 2 / b / 2 / c / 2 / d
    @test_nowarn @inferred (a * b) / (b * c)
    @test_nowarn @inferred (2a*b) / (4b * c)
    @test_nowarn @inferred (a^2 * b) / (a^3 * c)
end

@testset "Pow" begin
    @test_nowarn @inferred a ^ 2
    @test_nowarn @inferred 2 ^ a
    @test_nowarn @inferred a ^ b
    @test_nowarn @inferred (a * b) ^ 2
    @test_nowarn @inferred (a / b) ^ 4
    @test_nowarn @inferred (a / b) ^ c
    @test_nowarn @inferred (a ^ b) ^ c
end

# again in case stuff was precomputed in the previous tests
a = Sym{SymReal}(gensym(:a), type = Number)
b = Sym{SymReal}(gensym(:b), type = Number)
c = Sym{SymReal}(gensym(:c), type = Int)
d = Sym{SymReal}(gensym(:d), type = Real)

@testset "Arguments" begin
    @test_nowarn @inferred arguments(sin(a))
    @test_nowarn @inferred arguments(ifelse(a == b, b, c))
    @test_nowarn @inferred arguments(a + b + c + 2)
    @test_nowarn @inferred arguments(a * b * c * 2)
    @test_nowarn @inferred arguments(a ^ 2)
    @test_nowarn @inferred arguments(a / b)
end

@testset "hashequal" begin
    @test_nowarn @inferred hash(a)
    @test_nowarn @inferred hash(a + b)
    @test_nowarn @inferred hash(a * b)
    @test_nowarn @inferred hash(a ^ b)
    @test_nowarn @inferred hash(a / b)
    @test_nowarn @inferred hash(sin(a))
    @test_nowarn @inferred isequal(a, a)
    @test_nowarn @inferred isequal(a + b, a + b)
    @test_nowarn @inferred isequal(a * b, a * b)
    @test_nowarn @inferred isequal(a ^ b, a ^ b)
    @test_nowarn @inferred isequal(a / b, a / b)
    @test_nowarn @inferred isequal(sin(a), sin(a))
end

function foo end

@testset "`term`" begin
    @test_nowarn @inferred term(foo, a, b, c)
    @test_nowarn @inferred term(foo, a, b, c; type = Any)
    @test_nowarn @inferred term(foo, a, b, c; type = Number)
end

@testset "`maketerm`" begin
    @test_nowarn @inferred maketerm(BasicSymbolic{SymReal}, +, [a, b, c], nothing)
    @test_nowarn @inferred maketerm(BasicSymbolic{SymReal}, +, (a, b, c), nothing)
    @test_nowarn @inferred maketerm(BasicSymbolic{SymReal}, *, [a, b, c], nothing)
    @test_nowarn @inferred maketerm(BasicSymbolic{SymReal}, *, (a, b, c), nothing)
    @test_nowarn @inferred maketerm(BasicSymbolic{SymReal}, ^, [a, b], nothing)
    @test_nowarn @inferred maketerm(BasicSymbolic{SymReal}, ^, (a, b), nothing)
    @test_nowarn @inferred maketerm(BasicSymbolic{SymReal}, /, [a, b], nothing)
    @test_nowarn @inferred maketerm(BasicSymbolic{SymReal}, /, (a, b), nothing)
    @test_nowarn @inferred maketerm(BasicSymbolic{SymReal}, -, [a, b], nothing)
    @test_nowarn @inferred maketerm(BasicSymbolic{SymReal}, -, (a, b), nothing)
    @test_nowarn @inferred maketerm(BasicSymbolic{SymReal}, sin, [a], nothing)
    @test_nowarn @inferred maketerm(BasicSymbolic{SymReal}, sin, (a,), nothing)
    @test_nowarn @inferred maketerm(BasicSymbolic{SymReal}, ifelse, [a == b, b, c], nothing)
    @test_nowarn @inferred maketerm(BasicSymbolic{SymReal}, ifelse, (a == b, b, c), nothing)
end

@testset "`expand`" begin
    @test_nowarn @inferred expand((a + b) ^ 3 * d)
end

@testset "`simplify_div`" begin
    @test_nowarn @inferred SymbolicUtils.simplify_div((a ^ 2 + b^2 + 2a*b) / ((a + b) * (b + c)))
end

@testset "`flatten_fractions`" begin
    @test_nowarn @inferred flatten_fractions((1+(1+1/a)/a)/a)
end

@testset "`simplify_fractions`" begin
    @syms a b c d e f g h i
    ex = (f + ((((g*(c^2)*(e^2)) / d - e*h*(c^2)) / b + (-c*e*f*g) / d + c*e*i) /
              (i + ((c*e*g) / d - c*h) / b + (-f*g) / d) - c*e) / b +
         ((g*(f^2)) / d + ((-c*e*f*g) / d + c*f*h) / b - f*i) /
         (i + ((c*e*g) / d - c*h) / b + (-f*g) / d)) / d
    @test_nowarn @inferred simplify_fractions(ex)
end

@testset "`fraction_iszero`, `fraction_isone`" begin
    @syms a b c d e f g h i
    o = (d + (e*((c*(g + (-d*g) / d)) / (i + (-c*(h + (-e*g) / d)) / b + (-f*g) / d))) / b +
         (-f*(g + (-d*g) / d)) / (i + (-c*(h + (-e*g) / d)) / b + (-f*g) / d)) / d
    @test_nowarn @inferred fraction_iszero(o)
    @test_nowarn @inferred fraction_isone(o)
end

@testset "`simplify`" begin
    function random_term(len; atoms, funs, fallback_atom=1)
        xs = rand(atoms, len)
        while length(xs) > 1
            xs = map(Iterators.partition(xs, 2)) do xy
                x = xy[1]; y = get(xy, 2, fallback_atom)
                rand(funs)(x, y)
            end
        end
        xs[]
    end
    ex1 = random_term(10, atoms=[a, b, c, d, a^(-1), b^(-1), 1, 2.0], funs=[+, *])
    ex2 = random_term(10, atoms=[a, b, c, d, a^(-1), b^(-1), 1, 2.0], funs=[/, *])
    @test_nowarn @inferred simplify(ex1; simplify_fractions = true)
    @test_nowarn @inferred simplify(ex2; simplify_fractions = true)
    @test_nowarn @inferred simplify(ex1; simplify_fractions = false)
    @test_nowarn @inferred simplify(ex2; simplify_fractions = false)
end
