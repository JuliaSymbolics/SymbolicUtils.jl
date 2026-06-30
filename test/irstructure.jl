using SymbolicUtils
using SymbolicUtils: BasicSymbolic, IRStructure, IRSubstituter, populate_ir!, subset_ir, get_reachability, replace_node!, replace_edge!
import SymbolicUtils as SU
import Graphs

@syms t x y z(..) w[1:3] fn(::Number)
z = z(t)

function sanity_check(ir, expr)
    idx = ir[expr]
    @test isequal(ir[idx], expr)
    if !iscall(expr)
        # Ensure this is a leaf
        @test isempty(get_reachability(ir, idx))
        @test isempty(Graphs.outneighbors(ir.dependency_graph, idx))
        return
    end
    reference = Int[]
    # Arguments should all have smaller indices and be present in reachability
    for arg in arguments(expr)
        sanity_check(ir, arg)
        @test ir[arg] < idx
        @test ir[arg] in get_reachability(ir, idx)
        append!(reference, get_reachability(ir, ir[arg]))
        push!(reference, ir[arg])
    end
    if operation(expr) isa SU.BasicSymbolic{SymReal}
        op = operation(expr)::SU.BasicSymbolic{SymReal}
        @test ir[op] < idx
        @test ir[op] in get_reachability(ir, idx)
        append!(reference, get_reachability(ir, ir[op]))
        push!(reference, ir[op])
    end
    # Check reachability
    sort!(reference)
    unique!(reference)
    @test issetequal(get_reachability(ir, idx), reference)
end

@testset "Construction and invariants" begin
    ir = IRStructure{SymReal}()

    expr = x + 2y + 3sin(z + fn(w[1] + sum(w) * tanh(w'w)))
    idx = populate_ir!(ir, expr)
    @test length(ir) == idx
    sanity_check(ir, expr)

    # Invalid accesses should error
    expr2 = sin(x)
    @test_throws KeyError ir[expr2]
    @test_throws BoundsError ir[idx + 1]

    # `eachindex` should work and iterate integers
    @test all(Base.Fix2(isa, BasicSymbolic{SymReal}), [ir[i] for i in eachindex(ir)])

    # re-inserting the same expression should return the same index
    subidx = ir[2y]
    @test populate_ir!(ir, 2y) == subidx

    @testset "Uses hashconsing equality" begin
        ir2 = IRStructure{SymReal}()
        a = SU.Const{SymReal}(1)
        b = SU.Const{SymReal}(1.0)
        populate_ir!(ir2, a)
        populate_ir!(ir2, b)
        @test ir2[a] != ir2[b]
    end
end

@testset "`subset_ir`" begin
    expr1 = x + 2y + 3sin(z + fn(w[1] + sum(w) * tanh(w'w)))
    expr2 = 2x + 3y + 3sin(z + fn(w[1] + sum(w) * tanh(w'w)))
    ir1 = IRStructure{SymReal}()
    populate_ir!(ir1, expr1)
    populate_ir!(ir1, expr2)

    subexpr = 3sin(z + fn(w[1] + sum(w) * tanh(w'w)))
    subidx = ir1[subexpr]

    ir2 = subset_ir(ir1, [subexpr])
    ir_reference = IRStructure{SymReal}()
    populate_ir!(ir_reference, subexpr)
    @test length(ir2) == length(ir_reference)
    # SimpleDiGraph is lazy
    for i in eachindex(ir2)
        nbors = Graphs.outneighbors(ir2.dependency_graph, i)
        nbors_ref = Graphs.outneighbors(ir_reference.dependency_graph, i)
        @test isequal(nbors, nbors_ref)
    end
    @test isequal(ir2.symbols, ir_reference.symbols)
    @test isequal(ir2.definition, ir_reference.definition)
end

@testset "`search_variables!`" begin
    expr = x + 2y + 3sin(z + fn(w[1] + sum(w) * tanh(w'w)))
    ir = IRStructure{SymReal}()
    populate_ir!(ir, expr)

    buffer = Set{BasicSymbolic{SymReal}}()
    SU.search_variables!(buffer, ir, expr)
    buffer2 = empty(buffer)
    SU.search_variables!(buffer2, expr)
    @test issetequal(buffer, buffer)
end

@testset "`query`" begin
    expr = x + 2y + 3sin(z + fn(w[1] + sum(w) * tanh(w'w)))
    ir = IRStructure{SymReal}()
    populate_ir!(ir, expr)

    @test SU.query(isequal(y), ir, expr)
    @test !SU.query(isequal(w[2]), ir, expr)
    @test !SU.query(isequal(z), ir, expr; recurse = ex -> iscall(ex) && operation(ex) !== sin)
end

@testset "show" begin
    # Single leaf node: exact output check (indegree 0, never inlined)
    ir = IRStructure{SymReal}()
    populate_ir!(ir, x)
    @test sprint(show, ir) == "IRStructure with 1 node:\n  %1 = x\n"

    # Single-use nodes are inlined: x^2 + y has no sharing, collapses to one line
    ir = IRStructure{SymReal}()
    populate_ir!(ir, x^2 + y)
    output = sprint(show, ir)
    lines = split(output, '\n'; keepempty = false)
    @test startswith(lines[1], "IRStructure with ")
    @test endswith(lines[1], "nodes:")
    # Every definition line has the SSA format
    @test all(l -> occursin(r"^\s+%\d+ = ", l), lines[2:end])
    # With full inlining only the root remains, raw symbols appear inline
    @test occursin("x", lines[end]) && occursin("y", lines[end])

    # Shared subexpressions are kept as SSA vars and referenced by %i
    ir = IRStructure{SymReal}()
    populate_ir!(ir, x^2 + sin(x^2))  # x^2 used twice → stays as %1
    shared_output = sprint(show, ir)
    shared_lines = split(shared_output, '\n'; keepempty = false)
    # At least two printed lines (shared node + root)
    @test length(shared_lines) >= 3
    # Some line contains a call with an SSA ref as argument
    @test any(l -> occursin(r"\(%\d+", l), shared_lines)

    # Symbolic-op calls (default_is_atomic OR operation isa BasicSymbolic) are
    # printed as a single unit; their internal dependencies are never assigned SSA
    # variables.  z(..) creates a dependent variable; z(t) is a print-leaf.
    ir = IRStructure{SymReal}()
    populate_ir!(ir, z + 2t)   # z = z(t) defined at top of file
    atomic_output = sprint(show, ir)
    # z(t) appears literally, not decomposed as z(%1) or z(%i)
    @test occursin("z(t)", atomic_output)
    @test !occursin("z(%", atomic_output)
    # t only appears inside the print-leaf z(t) and once in *(2,t); with
    # visible ref-count 1 it is inlined, so no standalone "%i = t" line exists.
    @test !occursin(r"%\d+ = t\b", atomic_output)

    # Color: %i identifiers are highlighted yellow (ANSI code 33)
    colored = sprint(show, ir; context = :color => true)
    @test occursin("\e[33m%", colored)
    # Plain output (no color context) must not contain escape codes
    @test !occursin('\e', atomic_output)
end

@testset "Edge/outneighbor ordering invariant" begin
    # Verify that outneighbors of each callable node agree with the invariant:
    # - For a non-symbolic op:  outneighbors == [ir[arg] for arg in arguments(expr)]
    # - For a symbolic op:       outneighbors == [ir[op], ir[arg1], ir[arg2], ...]
    function check_edge_ordering_invariant(ir::IRStructure{T}) where {T}
        g = ir.dependency_graph
        for i in eachindex(ir)
            sym = ir[i]
            iscall(sym) || continue
            nbors = collect(Graphs.outneighbors(g, i))
            op = operation(sym)
            expected = Int32[]
            if op isa BasicSymbolic{T}
                push!(expected, ir.definition[op])
            end
            for arg in arguments(sym)
                arg isa BasicSymbolic{T} || continue
                push!(expected, ir.definition[arg])
            end
            @test nbors == expected
        end
    end

    @testset "Non-symbolic operation" begin
        ir = IRStructure{SymReal}()
        populate_ir!(ir, sin(x + y))
        check_edge_ordering_invariant(ir)
    end

    @testset "Symbolic operation prefixes arguments" begin
        @syms ordtest_fn(..)
        ir = IRStructure{SymReal}()
        expr = ordtest_fn(x, y)
        @test operation(expr) isa BasicSymbolic{SymReal}
        populate_ir!(ir, expr)
        check_edge_ordering_invariant(ir)
        # The symbolic op must be the first outneighbor after sorting
        idx = ir[expr]
        nbors = collect(Graphs.outneighbors(ir.dependency_graph, idx))
        @test nbors[1] == ir.definition[operation(expr)]
    end

    @testset "Complex expression" begin
        ir = IRStructure{SymReal}()
        # z = z(t) so operation(z) isa BasicSymbolic{SymReal}; exercises the symbolic-op path
        populate_ir!(ir, x + 2y + 3sin(z + fn(w[1] + sum(w) * tanh(w'w))))
        check_edge_ordering_invariant(ir)
    end

    @testset "After replace_node! (non-symbolic op)" begin
        ir = IRStructure{SymReal}()
        populate_ir!(ir, x + y)
        idx = ir[x + y]
        replace_node!(ir, x + y, x * y)
        check_edge_ordering_invariant(ir)
    end

    @testset "array_literal with duplicated arguments" begin
        # Const{T}([x, y, x]) creates an array_literal Term whose argument list is
        # [Const((3,)), x, y, x].  Because x appears twice, the dependency graph
        # must have two edges from the array_literal node to ir[x] (multi-edges).
        arr = SU.Const{SymReal}([x, y, x])
        @test operation(arr) === SymbolicUtils.array_literal
        ir = IRStructure{SymReal}()
        populate_ir!(ir, arr)
        check_edge_ordering_invariant(ir)
        arr_idx = ir[arr]
        nbors = collect(Graphs.outneighbors(ir.dependency_graph, arr_idx))
        x_idx = ir.definition[x]
        # x must appear at position 2 and 4 of outneighbors (after the size Const)
        @test count(==(x_idx), nbors) == 2
        @test nbors[2] == x_idx
        @test nbors[4] == x_idx
    end

    @testset "After replace_node! (symbolic op)" begin
        @syms ordtest_replace_fn(..)
        ir = IRStructure{SymReal}()
        populate_ir!(ir, x + y)
        idx = ir[x + y]
        replace_node!(ir, x + y, ordtest_replace_fn(x, y))
        check_edge_ordering_invariant(ir)
        nbors = collect(Graphs.outneighbors(ir.dependency_graph, idx))
        @test nbors[1] == ir.definition[ordtest_replace_fn]
    end
end

@testset "`replace_node!`" begin
    @testset "Leaf replacement" begin
        # Replacing a leaf: edges unchanged (early return after symbol update)
        ir = IRStructure{SymReal}()
        populate_ir!(ir, sin(x))
        x_idx = ir[x]
        n_before = length(ir)

        replace_node!(ir, x, y)

        @test isequal(ir[x_idx], y)
        @test length(ir) == n_before          # no new node created
        @test !haskey(ir.definition, x)       # old removed from definition
        @test ir.definition[y] == x_idx
        @test x_idx in ir.weak_definitions[y] # new registered at same index
        @test !isempty(ir.non_canonical_idxs)
        # leaf had no outgoing edges; they are still absent
        @test isempty(Graphs.outneighbors(ir.dependency_graph, x_idx))
    end

    @testset "Callable → callable, non-symbolic op" begin
        ir = IRStructure{SymReal}()
        populate_ir!(ir, x + y)
        idx    = ir[x + y]
        n_before = length(ir)

        replace_node!(ir, x + y, x * y)

        @test isequal(ir[idx], x * y)
        @test length(ir) == n_before          # no new node for the expression itself
        @test !haskey(ir.definition, x + y)
        @test ir.definition[x * y] == idx
        @test idx in ir.weak_definitions[x * y]
        # Nothing depends on `idx`, so the IR is still canonical
        @test isempty(ir.non_canonical_idxs)
        # outneighbors now match x*y's arguments in argument order
        nbors    = collect(Graphs.outneighbors(ir.dependency_graph, idx))
        expected = [ir.definition[arg] for arg in arguments(x * y)
                    if arg isa BasicSymbolic{SymReal}]
        @test nbors == expected
    end

    @testset "Callable → callable, symbolic op" begin
        @syms rn_symfn(..)
        ir = IRStructure{SymReal}()
        populate_ir!(ir, x + y)
        idx = ir[x + y]

        replace_node!(ir, x + y, rn_symfn(x, y))

        @test isequal(ir[idx], rn_symfn(x, y))
        @test !haskey(ir.definition, x + y)
        @test ir.definition[rn_symfn(x, y)] == idx
        @test isempty(ir.non_canonical_idxs)
        # symbolic op must be first outneighbor, then args in order
        nbors = collect(Graphs.outneighbors(ir.dependency_graph, idx))
        @test nbors[1] == ir.definition[rn_symfn]
        @test nbors[2] == ir.definition[x]
        @test nbors[3] == ir.definition[y]
    end

    @testset "Missing arguments are added to IR" begin
        ir = IRStructure{SymReal}()
        populate_ir!(ir, x + y)          # IR contains x, y, x+y; t absent
        @test !haskey(ir.definition, t)
        n_before = length(ir)

        replace_node!(ir, x + y, x + t)

        @test haskey(ir.definition, t)   # t was inserted by populate_ir! inside replace_node!
        @test length(ir) == n_before + 1
    end

    @testset "old weak_definitions entry is pruned" begin
        ir = IRStructure{SymReal}()
        populate_ir!(ir, x + y)
        idx = ir[x + y]
        @test idx in ir.weak_definitions[x + y]

        replace_node!(ir, x + y, x * y)

        old_defs = get(ir.weak_definitions, x + y, Int32[])
        @test !(idx in old_defs)
    end

    @testset "Old outgoing edges are removed" begin
        ir = IRStructure{SymReal}()
        populate_ir!(ir, x + y)
        idx   = ir[x + y]
        x_idx = ir[x]
        y_idx = ir[y]
        # Before: idx → x_idx and idx → y_idx
        @test x_idx in Graphs.outneighbors(ir.dependency_graph, idx)
        @test y_idx in Graphs.outneighbors(ir.dependency_graph, idx)

        replace_node!(ir, x + y, sin(x))   # different arg set

        nbors = collect(Graphs.outneighbors(ir.dependency_graph, idx))
        @test !(y_idx in nbors)             # y is no longer a dependency
        @test x_idx in nbors               # x is still used
    end
end

@testset "`get_canonical_expr!`" begin
    @testset "Canonical IR: returns ir[idx] directly" begin
        ir = IRStructure{SymReal}()
        expr = x + sin(y)
        populate_ir!(ir, expr)
        @test isempty(ir.non_canonical_idxs)
        idx = ir[expr]
        @test SU.get_canonical_expr!(ir, idx) === ir[idx]
    end

    @testset "Non-canonical, unaffected subtree: returns same object" begin
        ir = IRStructure{SymReal}()
        populate_ir!(ir, sin(x))
        populate_ir!(ir, cos(y))
        sin_idx = ir[sin(x)]
        replace_node!(ir, y, x)   # affects cos(y) only, not sin(x)
        @test !isempty(ir.non_canonical_idxs)
        @test SU.get_canonical_expr!(ir, sin_idx) === ir[sin_idx]
    end

    @testset "After leaf replacement: parent argument updated" begin
        ir = IRStructure{SymReal}()
        populate_ir!(ir, sin(x))
        sin_idx = ir[sin(x)]
        replace_node!(ir, x, y)
        @test !isempty(ir.non_canonical_idxs)
        @test isequal(SU.get_canonical_expr!(ir, sin_idx), sin(y))
    end

    @testset "After callable replacement: grandparent updated" begin
        ir = IRStructure{SymReal}()
        populate_ir!(ir, cos(x + y))
        cos_idx = ir[cos(x + y)]
        replace_node!(ir, x + y, x * y)
        @test !isempty(ir.non_canonical_idxs)
        @test isequal(SU.get_canonical_expr!(ir, cos_idx), cos(x * y))
    end

    @testset "Symbolic operation: arg replaced (n_drop=1 path)" begin
        # fn is a symbolic function; operation(fn(x)) isa BasicSymbolic, so the op
        # node is the first outneighbor and must be skipped when iterating args.
        ir = IRStructure{SymReal}()
        populate_ir!(ir, fn(x))
        fn_x_idx = ir[fn(x)]
        replace_node!(ir, x, y)
        @test !isempty(ir.non_canonical_idxs)
        @test isequal(SU.get_canonical_expr!(ir, fn_x_idx), fn(y))
    end
end

@testset "`IRSubstituter`" begin
    expr = x + 2y + 3sin(z + fn(w[1] + sum(w) * tanh(w'w)))
    ir = IRStructure{SymReal}()
    populate_ir!(ir, expr)

    rules = Dict(w => SU.Const{SymReal}(ones(3)))
    irsub = IRSubstituter{false}(ir, rules)
    sub = SU.Substituter{false}(rules)
    @test isequal(irsub(expr), sub(expr))

    ir = IRStructure{SymReal}()
    populate_ir!(ir, expr)

    rules = Dict(w => SU.Const{SymReal}(ones(3)))
    irsub = IRSubstituter{true}(ir, rules)
    sub = SU.Substituter{true}(rules)
    @test isequal(irsub(expr), sub(expr))

    @testset "On dependent variables" begin
        @syms t foo(..)
        foo = foo(t) # `foo` is now a dependent variable
        irsub = IRSubstituter{false}(ir, Dict(foo => 2t + 1))
        @test isequal(irsub(foo), 2t+1)
    end

    @testset "On symbolic functions" begin
        @syms foo(t)
        irsub = IRSubstituter{false}(ir, Dict(foo => SU.Const{SymReal}(sin)))
        @test isequal(irsub(foo(t + 1)), sin(t + 1))
    end
end

# Helper: build an IRStructure for `expr` with the ordering invariant intentionally
# violated. Expressions are added in reverse of the natural postorder (roots first),
# so parents end up at lower indices than their children.
function make_reversed_ir(T, root_expr::BasicSymbolic)
    ir_normal = IRStructure{T}()
    populate_ir!(ir_normal, root_expr)
    n = length(ir_normal)

    dep_graph = SymbolicUtils.OrderedDiGraph{Int32}(n)
    reversed_symbols = reverse(ir_normal.symbols)  # root at index 1, leaves at end
    reversed_def = IdDict{BasicSymbolic{T}, Int32}()
    for (i, sym) in enumerate(reversed_symbols)
        reversed_def[sym] = i
    end
    for (i, sym) in enumerate(reversed_symbols)
        if iscall(sym)
            for arg in arguments(sym)
                arg isa BasicSymbolic{T} || continue
                haskey(reversed_def, arg) || continue
                Graphs.add_edge!(dep_graph, i, reversed_def[arg])
            end
            op = operation(sym)
            if op isa BasicSymbolic{T} && haskey(reversed_def, op)
                Graphs.add_edge!(dep_graph, i, reversed_def[op])
            end
        end
    end
    IRStructure{T}(dep_graph, reversed_symbols, reversed_def, Dict{BasicSymbolic{T}, Vector{Int32}}(), BitVector(), Int32[], BitSet())
end

@testset "Out-of-order IRStructure" begin
    # Use a simple expression so the reversed layout is easy to reason about.
    # x + y: normal layout x=1,y=2,x+y=3; reversed: x+y=1,y=2,x=3.
    expr = x + y
    ir = make_reversed_ir(SymReal, expr)

    # Verify the invariant is intentionally violated
    @test ir[expr] < ir[x]
    @test ir[expr] < ir[y]

    # get_reachability returns indices of x and y (in some topological order)
    reach = get_reachability(ir, ir[expr])
    @test Set(reach) == Set([ir[x], ir[y]])

    # search_variables! finds both variables
    buffer = Set{BasicSymbolic{SymReal}}()
    SU.search_variables!(buffer, ir, expr)
    @test x in buffer
    @test y in buffer

    # query detects x but not an unrelated symbol
    @test SU.query(isequal(x), ir, expr)
    @test !SU.query(isequal(z), ir, expr)

    # show / print_ir produce valid output without errors
    ir_output = sprint(show, ir)
    @test occursin(r"IRStructure with \d+ node", ir_output)
    @test occursin(r"%\d+ = ", ir_output)

    # subset_ir extracts the full sub-expression correctly
    ir_sub = subset_ir(ir, [expr])
    @test length(ir_sub) == 3  # x, y, x+y

    # IRSubstituter applies substitution correctly on out-of-order IR
    rules = Dict{BasicSymbolic{SymReal}, BasicSymbolic{SymReal}}(x => 2y)
    irsub = IRSubstituter{false}(ir, rules)
    sub = SU.Substituter{false}(rules)
    @test isequal(irsub(expr), sub(expr))
end

@testset "`IRSubstituter` doesn't process filtered subtrees" begin
    # It used to still give the correct result, but processed (and thus cached)
    # subtrees which are filtered out.
    @syms x y
    filterer = x -> iscall(x) && operation(x) !== sin
    expr = sin(x) + cos(y)
    ir = IRStructure{SymReal}()
    subber = IRSubstituter{false}(ir, Dict(y => x); filterer)
    res = subber(expr)
    @test isequal(res, sin(x) + cos(x))
    x_idx = ir[x]
    @test !haskey(subber.cache, x_idx)
end

@testset "Calling `replace_node!` when `new` already exists in `IRStructure`" begin
    @syms x y z
    ir = IRStructure{SymReal}()
    xidx = populate_ir!(ir, x)
    yidx = populate_ir!(ir, y)
    zidx = populate_ir!(ir, z)
    replace_node!(ir, x, y)
    @test !haskey(ir, x)
    @test isequal(ir[xidx], y)
    @test ir[xidx] !== y # different metadata
    @test ir[ir[xidx]] == xidx
    @test ir[ir[yidx]] == yidx
    replace_node!(ir, z, y)
    @test !haskey(ir, z)
    @test isequal(ir[zidx], y)
    @test ir[zidx] !== y # different metadata
    @test ir[ir[zidx]] == zidx
    @test ir[ir[yidx]] == yidx

    @testset "`isconst(new)`" begin
        @syms x y z
        ir = IRStructure{SymReal}()
        xidx = populate_ir!(ir, x)
        yidx = populate_ir!(ir, y)
        zidx = populate_ir!(ir, z)
        r = SymbolicUtils.Const{SymReal}(0)
        replace_node!(ir, x, r)
        replace_node!(ir, y, r)
        @test operation(ir[yidx]) === identity
    end
end

@testset "`replace_node!` replacing `!iscall(old)` with `iscall(new)`" begin
    @syms x
    ir = IRStructure{SymReal}()
    xidx = populate_ir!(ir, x)
    @test length(ir) == 1
    replace_node!(ir, x, sin(x))
    @test length(ir) == 2
    @test ir[x] != xidx
    @test isequal(ir[xidx], sin(x))
    @test collect(Graphs.outneighbors(ir.dependency_graph, xidx)) == [ir[x]]
end

@testset "Issue#981: `get_canonical_expr!` folding in `maketerm` resulting in different arguments" begin
    @syms a::Real b::Real a2::Real
    a = SU.unwrap(a); b = SU.unwrap(b); a2 = SU.unwrap(a2)

    # An *unfolded* multiplication node  M = (-1) * (a / b)
    # (raw `Term` ctor so it is not eagerly folded into a Div).
    M = SU.Term{SymReal}(*, Any[SU.Const{SymReal}(-1), a / b]; type = Real)

    ir  = IRStructure{SymReal}()
    idx = populate_ir!(ir, M)

    # Break canonical form (`a` is a descendant of M via a/b), then canonicalize.
    replace_node!(ir, a, a2)
    SU.get_canonical_expr!(ir, idx)

    node  = ir[idx]
    args  = collect(arguments(node))
    edges = [ir[j] for j in Graphs.outneighbors(ir.dependency_graph, idx)]
    @test isequal(args, edges)
    expr1 = SU.Code.fast_toexpr(ir[idx], ir, Dict{Any,Any}())
    Base.remove_linenums!(expr1)
    expr2 = SU.Code.fast_toexpr((-1)*(a2/b), Dict{Any,Any}())
    Base.remove_linenums!(expr2)
    @test isequal(repr(expr1), repr(expr2))
end

@testset "`IRSubstituter` doesn't cache filtered expressions" begin
    @syms t::Real a::Real b(..)::Real
    expr = a + b(t)
    @test !SU.default_substitute_filter(b(t))
    rules = Dict{typeof(a), typeof(a)}(a => 2a)
    ir = IRStructure{SymReal}()
    subber = IRSubstituter{false}(ir, rules)
    subber(expr)
    @test !haskey(subber.cache, ir[b(t)])
    subber(t)
    @test !haskey(subber.cache, ir[t])
end

@testset "`replace_edge!`" begin
    @testset "Basic single-edge replacement" begin
        # sin(x): sin_idx → x_idx; replace with sin_idx → y_idx
        ir = IRStructure{SymReal}()
        populate_ir!(ir, sin(x))
        sin_idx = ir[sin(x)]
        x_idx   = ir[x]
        y_idx   = populate_ir!(ir, y)
        g = ir.dependency_graph

        @test collect(Graphs.outneighbors(g, sin_idx)) == [x_idx]
        @test isempty(ir.non_canonical_idxs)

        replace_edge!(ir, sin_idx, x_idx, y_idx)

        @test collect(Graphs.outneighbors(g, sin_idx)) == [y_idx]
        @test sin_idx in ir.non_canonical_idxs
    end

    @testset "Only matching edges are replaced, others preserved" begin
        # x + y: plus_idx → [x_idx, y_idx]; replace x_idx with z_idx
        ir = IRStructure{SymReal}()
        populate_ir!(ir, x + y)
        plus_idx = ir[x + y]
        x_idx    = ir[x]
        y_idx    = ir[y]
        z_idx    = populate_ir!(ir, z)
        g = ir.dependency_graph

        replace_edge!(ir, plus_idx, x_idx, z_idx)

        nbors = collect(Graphs.outneighbors(g, plus_idx))
        @test z_idx in nbors          # old x_idx replaced by z_idx
        @test y_idx in nbors          # y edge untouched
        @test !(x_idx in nbors)       # original x edge removed
        @test length(nbors) == 2      # edge count preserved
    end

    @testset "Multiple identical edges: all replaced" begin
        # Build a Term with x appearing twice as an argument, producing two edges to x_idx.
        @syms arr_x::Real arr_y::Real arr_z::Real
        arr_x = SU.unwrap(arr_x); arr_y = SU.unwrap(arr_y); arr_z = SU.unwrap(arr_z)
        # Term{SymReal}(+, [arr_x, arr_x]) creates x+x unfolded (two edges to arr_x)
        dup_expr = SU.Term{SymReal}(+, Any[arr_x, arr_x]; type = Real)
        ir = IRStructure{SymReal}()
        populate_ir!(ir, dup_expr)
        dup_idx = ir[dup_expr]
        x_idx   = ir[arr_x]
        z_idx   = populate_ir!(ir, arr_z)
        g = ir.dependency_graph

        # Confirm two edges to arr_x exist before replacement
        nbors_before = collect(Graphs.outneighbors(g, dup_idx))
        @test count(==(x_idx), nbors_before) == 2

        replace_edge!(ir, dup_idx, x_idx, z_idx)

        nbors_after = collect(Graphs.outneighbors(g, dup_idx))
        @test count(==(z_idx), nbors_after) == 2   # both edges now point to z
        @test !(x_idx in nbors_after)               # no residual edge to x
        @test length(nbors_after) == 2              # edge count preserved
        @test dup_idx in ir.non_canonical_idxs
    end

    @testset "get_canonical_expr! after replace_edge!" begin
        # After redirecting an edge, get_canonical_expr! should reflect the new arg.
        ir = IRStructure{SymReal}()
        populate_ir!(ir, sin(x))
        sin_idx = ir[sin(x)]
        x_idx   = ir[x]
        y_idx   = populate_ir!(ir, y)

        replace_edge!(ir, sin_idx, x_idx, y_idx)

        @test isequal(SU.get_canonical_expr!(ir, sin_idx), sin(y))
        # IR should be canonical again after the call
        @test isempty(ir.non_canonical_idxs)
    end

    @testset "old_dst == new_dst is a pure no-op" begin
        # When old_dst === new_dst the function returns immediately — edges and
        # non_canonical_idxs are both unchanged.
        ir = IRStructure{SymReal}()
        populate_ir!(ir, x + y)
        plus_idx = ir[x + y]
        x_idx    = ir[x]
        g = ir.dependency_graph
        nbors_before = collect(Graphs.outneighbors(g, plus_idx))

        replace_edge!(ir, plus_idx, x_idx, x_idx)

        @test collect(Graphs.outneighbors(g, plus_idx)) == nbors_before
        @test isempty(ir.non_canonical_idxs)
    end

    @testset "no edge to old_dst is a pure no-op" begin
        # When src has no edge to old_dst the function returns without mutating anything.
        ir = IRStructure{SymReal}()
        populate_ir!(ir, sin(x))
        sin_idx = ir[sin(x)]
        x_idx   = ir[x]
        y_idx   = populate_ir!(ir, y)   # y is in the IR but not a neighbor of sin
        g = ir.dependency_graph
        nbors_before = collect(Graphs.outneighbors(g, sin_idx))

        replace_edge!(ir, sin_idx, y_idx, x_idx)   # y_idx not an outneighbor of sin_idx

        @test collect(Graphs.outneighbors(g, sin_idx)) == nbors_before
        @test isempty(ir.non_canonical_idxs)
    end
end
