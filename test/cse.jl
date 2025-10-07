using SymbolicUtils, SymbolicUtils.Code, SparseArrays, Test
using SymbolicUtils.Code: topological_sort
using RuntimeGeneratedFunctions

RuntimeGeneratedFunctions.init(@__MODULE__)

@testset "CSE" begin
    @syms x
    t = cse(hypot(hypot(cos(x), sin(x)), atan(cos(x), sin(x))))

    @test t isa Let
    @test length(t.pairs) == 5
    @test SymbolicUtils.query(isequal(t.pairs[3].lhs), t.pairs[5].rhs)
    @test SymbolicUtils.query(isequal(t.pairs[4].lhs), t.pairs[5].rhs)
end

@testset "DAG CSE" begin
    @syms a b
    expr = sin(a + b) * (a + b)
    sorted_nodes = topological_sort(expr)
    @test length(sorted_nodes) == 3
    node = sorted_nodes[1].rhs
    @test operation(node) === (+) && issetequal(arguments(node), [a, b])
    @test isequal(sin(sorted_nodes[1].lhs), sorted_nodes[2].rhs)

    expr = (a + b)^(a + b)
    sorted_nodes = topological_sort(expr)
    @test length(sorted_nodes) == 2
    node = sorted_nodes[1].rhs
    @test operation(node) === (+) && issetequal(arguments(node), [a, b])
    ab_node = sorted_nodes[1].lhs
    @test isequal(term(^, ab_node, ab_node), sorted_nodes[2].rhs)
    let_expr = cse(expr)
    @test length(let_expr.pairs) == 2
    node = let_expr.pairs[1].rhs
    @test operation(node) === (+) && issetequal(arguments(node), [a, b])
    corresponding_sym = let_expr.pairs[1].lhs
    @test isequal(let_expr.pairs[end].rhs, term(^, corresponding_sym, corresponding_sym))

    expr = a + b
    sorted_nodes = topological_sort(expr)
    @test length(sorted_nodes) == 1
    node = sorted_nodes[1].rhs
    @test operation(node) === (+) && issetequal(arguments(node), [a, b])
    let_expr = cse(expr)
    @test length(let_expr.pairs) == 1
    node = let_expr.pairs[end].rhs
    @test operation(node) === (+) && issetequal(arguments(node), [a, b])
    
    expr = a
    sorted_nodes = topological_sort(expr)
    @test isempty(sorted_nodes)
    let_expr = cse(expr)
    @test isequal(let_expr, expr)

    # array symbolics
    # https://github.com/JuliaSymbolics/SymbolicUtils.jl/pull/688#pullrequestreview-2554931739
    @syms a b c
    function foo(args...)
        return args
    end
    ex = term(foo, [a^2 + b^2, b^2 + c], (a^2 + b^2, b^2 + c), c; type = Real)
    sorted_nodes = topological_sort(ex)
    @test length(sorted_nodes) == 10
    @test operation(sorted_nodes[8].rhs) === hvncat
    @test operation(sorted_nodes[9].rhs) === tuple
    expr = quote
        a = 1
        b = 2
        c = 3
        $(toexpr(cse(ex)))
    end
    vals = eval(expr)
    @test vals[1] == [1 + 4, 4 + 3]
    @test vals[2] == (1 + 4, 4 + 3)
    @test vals[3] == 3
end

@testset "Expr" begin
    ex = :(a^2 + sin(a^2))
    @test isequal(cse(ex), ex)
    ex = LiteralExpr(ex)
    @test isequal(cse(ex), ex)
end

@testset "Tuple" begin
    @syms a b
    ex = (a^2 + sin(a^2), sin(a^2) + b^2, b^2 + sin(b^2))
    csex = cse(ex)
    i, j, k = findfirst.(isequal.(csex.body) .∘ Code.lhs, (csex.pairs,))
    @test i !== nothing
    @test j !== nothing
    @test k !== nothing
    csex = Let(csex.pairs, MakeTuple(csex.body), false)
    expr = quote
        let a = 1, b = 2
            $(toexpr(csex))
        end
    end
    csex2 = cse(MakeTuple(collect(ex)))
    expr2 = quote
        let a = 1, b = 2
            $(toexpr(csex2))
        end
    end
    @test collect(eval(expr)) ≈ [1 + sin(1), sin(1) + 4, 4 + sin(4)]
    @test collect(eval(expr)) ≈ collect(eval(expr2))
end

@testset "MakeArray, SetArray, MakeSparseArray, AtIndex" begin
    @syms a b c
    arr = [a^2 + sin(a * b) sin(a * b) + c^2
           c^2 + sin(b * c) sin(b * c) + a^2]
    marr = MakeArray(arr, Array)
    sparr = sparse([1, 2, 3, 4], [1, 2, 3, 4], vec(arr))
    msparr = MakeSparseArray(sparr)
    sarr = SetArray(false, :buffer, [[a^2 + c^2], AtIndex(3, arr), AtIndex(4, msparr)], true)

    csex = cse(sarr)
    # test that simple array is CSEd
    @test findfirst(isequal(csex.body.elems[1][1]), Code.lhs.(csex.pairs)) !== nothing
    # test that `AtIndex` is CSEd
    i, j, k, l = findfirst.(isequal.(csex.body.elems[2].elem), (Code.lhs.(csex.pairs),))
    @test i !== nothing
    @test j !== nothing
    @test k !== nothing
    @test l !== nothing
    # test that `MakeSpareArray` is CSEd, and re-uses the values from the `MakeArray`
    ii, jj, kk, ll = findfirst.(isequal.(findnz(csex.body.elems[3].elem.array)[3]), (Code.lhs.(csex.pairs),))
    @test i == ii
    @test j == jj
    @test k == kk
    @test l == ll
    expr = quote
        let a = 1, b = 2, c = 3, buffer = Any[0, "A", 0, 0]
            $(toexpr(csex))
        end
    end
    val = eval(expr)
    @test val[1] == [10]
    @test val[2] == "A"
    result = [1 + sin(2) sin(2) + 9
              9 + sin(6) sin(6) + 1]
    @test val[3] == result
    @test val[4] == sparse([1, 2, 3, 4], [1, 2, 3, 4], vec(result))
end

@testset "Let, Func, Assignment, DestructuredArgs" begin
    @syms a b c d::Array e f
    fn = Func([a, DestructuredArgs([b, c])], [], Let([Assignment(d, [a^2 + b^2, b^2 + c^2]), DestructuredArgs([e, f], term(broadcast, *, 2, d))], a^2 + b^2 + e + f))
    csex = cse(fn)
    sexprs = csex.body.pairs
    assignments = filter(x -> x isa Assignment, sexprs)
    didx = findfirst(x -> isequal(x.lhs, d), sexprs)
    # the array in the assignment should be CSEd
    i, j = findfirst.(isequal.(sexprs[didx].rhs), (Code.lhs.(assignments),))
    @test i !== nothing
    @test j !== nothing
    didx = findfirst(x -> x isa DestructuredArgs, sexprs)
    @test sexprs[didx] isa DestructuredArgs
    @test findfirst(isequal(sexprs[didx].name), Code.lhs.(assignments)) !== nothing

    rgf = @RuntimeGeneratedFunction(toexpr(csex))
    trueval = let a = 1,
        b = 2,
        c = 3,
        tmp1 = b^2,
        tmp2 = a^2,
        tmp3 = tmp1 + tmp2,
        tmp4 = c^2,
        tmp5 = tmp1 + tmp4,
        d = [tmp3, tmp5],
        tmp6 = 2 .* d,
        e = tmp6[1],
        f = tmp6[2],
        tmp7 = f + tmp1 + tmp2 + e
        tmp7
    end
    @test rgf(1, [2, 3]) == trueval
end

@testset "SpawnFetch" begin
    @syms a b c d
    fn = Func([c, d], [], c^2 + d^2 + sin(c^2))
    ex = SpawnFetch{Multithreaded}([fn], [[a^2 + b^2, sin(a^2)]], only)
    csex = cse(ex)
    # arguments to the inner function are CSEd
    i, j = findfirst.(isequal.(csex.body.args[1]), (Code.lhs.(csex.pairs),))
    @test i !== nothing
    @test j !== nothing
    innerkeys = Code.lhs.(csex.body.exprs[1].body.pairs)
    @test findfirst(isequal(csex.body.exprs[1].body.body), innerkeys) !== nothing

    expr = quote
        let a = 1, b = 2
            $(toexpr(csex))
        end
    end
    trueval = let a = 1, b = 2, c = a^2 + b^2, d = sin(a^2)
        c^2 + d^2 + sin(c^2)
    end
    @test eval(expr) == trueval
    innerfn = csex.body.exprs[1]

    # test inner function is CSEd independently
    rgf = @RuntimeGeneratedFunction(toexpr(innerfn))
    @test rgf(5, sin(1)) == trueval
end

@testset "ForLoop" begin
    @syms a b c::Array
    ex = ForLoop(a, term(range, b^2, b^2 + 3), SetArray(false, c, [AtIndex(a, a^2 + sin(a^2))]))
    csex = cse(ex)
    @test findfirst(isequal(csex.body.range), Code.lhs.(csex.pairs)) !== nothing
    @test findfirst(isequal(csex.body.body.body.elems[1].elem), Code.lhs.(csex.body.body.pairs)) !== nothing
    expr = quote
        let b = 2, c = zeros(10)
            $(toexpr(ex))
            c
        end
    end
    arr = eval(expr)
    @test arr[4] == 4^2 + sin(4^2)
    @test arr[5] == 5^2 + sin(5^2)
    @test arr[6] == 6^2 + sin(6^2)
    @test arr[7] == 7^2 + sin(7^2)
    @test all(iszero, arr[1:3])
    @test all(iszero, arr[8:end])
end

@testset "CSE doesn't affect ranges" begin
    @syms x::Array
    t = term(view, x, 1:3)
    fnexpr = Func([x], [], t)
    fn1 = @RuntimeGeneratedFunction(toexpr(fnexpr))
    fn2 = @RuntimeGeneratedFunction(cse(toexpr(fnexpr)))
    @test fn1(ones(5)) == fn2(ones(5))
end

@testset "Tuples and arrays of `Symbol`s aren't symbolic" begin
    @syms x y
    f(a, b, c) = a + b + length(c)
    ex = term(f, x, y, (:a, :b, :c))
    expr = quote
        let x = 1, y = 2
            $(toexpr(cse(ex)))
        end
    end
    @test eval(expr) == 6
    ex = term(f, x, y, [:a, :b, :c])
    expr = quote
        let x = 1, y = 2
            $(toexpr(cse(ex)))
        end
    end
    @test eval(expr) == 6
end
