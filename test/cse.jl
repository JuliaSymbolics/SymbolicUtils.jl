using SymbolicUtils, SymbolicUtils.Code, Test
using RuntimeGeneratedFunctions

RuntimeGeneratedFunctions.init(@__MODULE__)

@testset "CSE" begin
    @syms x
    t = cse(hypot(hypot(cos(x), sin(x)), atan(cos(x), sin(x))))

    @test t isa Let
    @test length(t.pairs) == 5
    @test occursin(t.pairs[3].lhs, t.pairs[5].rhs)
    @test occursin(t.pairs[4].lhs, t.pairs[5].rhs)
end

@testset "DAG CSE" begin
    @syms a b
    expr = sin(a + b) * (a + b)
    sorted_nodes = topological_sort(expr)
    @test length(sorted_nodes) == 3
    @test isequal(sorted_nodes[1].rhs, term(+, a, b))
    @test isequal(sin(sorted_nodes[1].lhs), sorted_nodes[2].rhs)

    expr = (a + b)^(a + b)
    sorted_nodes = topological_sort(expr)
    @test length(sorted_nodes) == 2
    @test isequal(sorted_nodes[1].rhs, term(+, a, b))
    ab_node = sorted_nodes[1].lhs
    @test isequal(term(^, ab_node, ab_node), sorted_nodes[2].rhs)
    let_expr = cse(expr)
    @test length(let_expr.pairs) == 2
    @test isequal(let_expr.pairs[1].rhs, term(+, a, b))
    corresponding_sym = let_expr.pairs[1].lhs
    @test isequal(let_expr.pairs[end].rhs, term(^, corresponding_sym, corresponding_sym))

    expr = a + b
    sorted_nodes = topological_sort(expr)
    @test length(sorted_nodes) == 1
    @test isequal(sorted_nodes[1].rhs, term(+, a, b))
    let_expr = cse(expr)
    @test length(let_expr.pairs) == 1
    @test isequal(let_expr.pairs[end].rhs, term(+, a, b))
    
    expr = a
    sorted_nodes = topological_sort(expr)
    @test isempty(sorted_nodes)
    let_expr = cse(expr)
    @test isempty(let_expr.pairs)
    @test isequal(let_expr.body, a)

    # array symbolics
    # https://github.com/JuliaSymbolics/SymbolicUtils.jl/pull/688#pullrequestreview-2554931739
    @syms a b c
    function foo(args...)
        return args
    end
    ex = term(foo, [a^2 + b^2, b^2 + c], (a^2 + b^2, b^2 + c), c; type = Real)
    sorted_nodes = topological_sort(ex)
    @test length(sorted_nodes) == 7
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
    @test isequal(cse(ex).body, ex)
    ex = LiteralExpr(ex)
    @test isequal(cse(ex).body, ex)
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
    sarr = SetArray(false, :buffer, [[a^2 + c^2], AtIndex(3, arr), AtIndex(4, msparr)])

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
            buffer
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

    @test length(csex.body.pairs) == 9
    sexprs = csex.body.pairs
    assignments = filter(x -> x isa Assignment, sexprs)
    @test sexprs[6].lhs === d
    # the array in the assignment should be CSEd
    i, j = findfirst.(isequal.(sexprs[6].rhs), (Code.lhs.(assignments),))
    @test i !== nothing
    @test j !== nothing
    @test sexprs[8] isa DestructuredArgs
    @test isequal(sexprs[8].name, sexprs[7].lhs)

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
