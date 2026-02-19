module Code

using StaticArraysCore, SparseArrays, LinearAlgebra, NaNMath, SpecialFunctions,
      DocStringExtensions

export toexpr, Assignment, (←), Let, Func, DestructuredArgs, LiteralExpr,
       SetArray, MakeArray, MakeSparseArray, MakeTuple, AtIndex,
       SpawnFetch, Multithreaded, ForLoop, cse

export OptimizationRule, substitute_in_ir, apply_optimization_rules

import ..SymbolicUtils
import ..SymbolicUtils.Rewriters
import SymbolicUtils: @matchable, BasicSymbolic, Sym, Term, iscall, operation, arguments, issym,
                      symtype, sorted_arguments, metadata, isterm, term, maketerm, unwrap_const,
                      ArgsT, Const, SymVariant, _is_array_of_symbolics, _is_tuple_of_symbolics,
                      ArrayOp, isarrayop, IdxToAxesT, ROArgsT, shape, Unknown, ShapeVecT, BSImpl,
                      search_variables!, _is_index_variable, RangesT, IDXS_SYM, is_array_shape,
                      symtype, vartype, add_worker, search_variables!, @union_split_smallvec,
                      ArrayMaker, TypeT, ShapeT, SymReal, SafeReal, TreeReal, _unreachable, unwrap,
                      AddMulVariant, _isone, _iszero
using Moshi.Match: @match
import SymbolicIndexingInterface: symbolic_type, NotSymbolic

##== state management ==##

struct NameState
    rewrites::Dict{Any, Any}
end
NameState() = NameState(Dict{Any, Any}())
function union_rewrites!(n, ts)
    for t in ts
        n[t] = Symbol(string(t)::String)
    end
end

struct LazyState
    ref::Ref{Any}
end
LazyState() = LazyState(Ref{Any}(nothing))

function Base.get(st::LazyState)
    s = getfield(st, :ref)[]
    s === nothing ? getfield(st, :ref)[] = NameState() : s
end

@inline Base.getproperty(st::LazyState, f::Symbol) = f==:symbolify ?  getproperty(st, :rewrites) : getproperty(get(st), f)

##========================##

abstract type CodegenPrimitive end

function manual_dispatch_toexpr(@nospecialize(x), st)
    if x isa BasicSymbolic{SymReal}
        toexpr(x, st)
    elseif x isa Vector{BasicSymbolic{SymReal}}
        toexpr(x, st)
    elseif x isa Matrix{BasicSymbolic{SymReal}}
        toexpr(x, st)
    elseif x isa Symbol
        toexpr(x, st)
    elseif x isa Expr
        toexpr(x, st)
    elseif x isa Let
        toexpr(x, st)
    elseif x isa Assignment
        toexpr(x, st)
    elseif x isa DestructuredArgs
        toexpr(x, st)
    elseif x isa MakeArray
        toexpr(x, st)
    elseif x isa SetArray
        toexpr(x, st)
    elseif x isa SetArray
        toexpr(x, st)
    else
        toexpr(x, st)
    end
end

"""
    toexpr(ex, [st,])

Convert a symbolic expression into an `Expr`, suitable to be passed into `eval`.

For example,

```julia-repl
julia> @syms a b
(a, b)

julia> toexpr(a+b)
:((+)(a, b))

julia> toexpr(a+b) |> dump
Expr
  head: Symbol call
  args: Array{Any}((3,))
    1: + (function of type typeof(+))
    2: Symbol a
    3: Symbol b
```

Note that the function is an actual function object.

For more complex expressions, see other code-related combinators,

Namely `Assignment`, `Let`, `Func`, `SetArray`, `MakeArray`, `MakeSparseArray` and
`MakeTuple`.

To make your own type convertible to Expr using `toexpr` define `toexpr(x, st)` and
forward the state `st` in internal calls to `toexpr`. `st` is state used to know
when to leave something like `y(t)` as it is or when to make it `var"y(t)"`. E.g.
when `y(t)` is itself the argument of a function rather than `y`.

"""
toexpr(x) = toexpr(x, LazyState())

@matchable struct Assignment <: CodegenPrimitive
    lhs
    rhs
end

"""
    Assignment(lhs, rhs)

An assignment expression. Shorthand `lhs ← rhs` (`\\leftarrow`)
"""
Assignment

function search_variables!(buffer, asg::Assignment; kw...)
    lhs = asg.lhs
    rhs = asg.rhs
    if lhs isa BasicSymbolic{SymReal}
        search_variables!(buffer, lhs; kw...)
    elseif lhs isa BasicSymbolic{SafeReal}
        search_variables!(buffer, lhs; kw...)
    elseif lhs isa BasicSymbolic{TreeReal}
        search_variables!(buffer, lhs; kw...)
    elseif lhs isa Symbol
    else
        search_variables!(buffer, lhs; kw...)
    end
    if rhs isa BasicSymbolic{SymReal}
        search_variables!(buffer, rhs; kw...)
    elseif rhs isa BasicSymbolic{SafeReal}
        search_variables!(buffer, rhs; kw...)
    elseif rhs isa BasicSymbolic{TreeReal}
        search_variables!(buffer, rhs; kw...)
    elseif rhs isa Vector{BasicSymbolic{SymReal}}
        search_variables!(buffer, rhs; kw...)
    elseif rhs isa Vector{BasicSymbolic{SafeReal}}
        search_variables!(buffer, rhs; kw...)
    elseif rhs isa Vector{BasicSymbolic{TreeReal}}
        search_variables!(buffer, rhs; kw...)
    elseif rhs isa Matrix{BasicSymbolic{SymReal}}
        search_variables!(buffer, rhs; kw...)
    elseif rhs isa Matrix{BasicSymbolic{SafeReal}}
        search_variables!(buffer, rhs; kw...)
    elseif rhs isa Matrix{BasicSymbolic{TreeReal}}
        search_variables!(buffer, rhs; kw...)
    elseif rhs isa Symbol
    else
        search_variables!(buffer, rhs; kw...)
    end
end

lhs(a::Assignment) = a.lhs
rhs(a::Assignment) = a.rhs

const (←) = Assignment

Base.convert(::Type{Assignment}, p::Pair) = Assignment(pair[1], pair[2])

function toexpr(a::Assignment, st)
    return Expr(:(=), manual_dispatch_toexpr(a.lhs, st), manual_dispatch_toexpr(a.rhs, st))
end

const NaNMathFuns = (
    sin,
    cos,
    tan,
    asin,
    acos,
    acosh,
    atanh,
    log,
    log2,
    log10,
    lgamma,
    log1p,
    sqrt,
)

function function_to_expr_no_nanmath(@nospecialize(op), O::BasicSymbolic{T}, st) where {T}
    expr = Expr(:call)
    if op isa BasicSymbolic{T}
        push!(expr.args, manual_dispatch_toexpr(op, st))
    else
        push!(expr.args, op)
    end
    args = parent(arguments(O))
    @union_split_smallvec args for arg in args
        push!(expr.args, toexpr(arg, st))
    end
    return expr
end

function function_to_expr(@nospecialize(op), O, st)
    # Avoid using `op in NaNMathFuns` since that is dynamic dispatch.
    # Also avoid using `nameof(op)` for the same reason.
    if !get(st.rewrites, :nanmath, false)::Bool
        return function_to_expr_no_nanmath(op, O, st)
    elseif op === sin
        name = :sin
    elseif op === cos
        name = :cos
    elseif op === tan
        name = :tan
    elseif op === asin
        name = :asin
    elseif op === acos
        name = :acos
    elseif op === acosh
        name = :acosh
    elseif op === atanh
        name = :atanh
    elseif op === log
        name = :log
    elseif op === log2
        name = :log2
    elseif op === log10
        name = :log10
    elseif op === lgamma
        name = :lgamma
    elseif op === log1p
        name = :log1p
    elseif op === sqrt
        name = :sqrt
    else
        return function_to_expr_no_nanmath(op, O, st)
    end
    fun = GlobalRef(NaNMath, name)
    return function_to_expr_no_nanmath(fun, O, st)
end

function function_to_expr(@nospecialize(op::SymbolicUtils.Mapper), O, st)
    out = get(st.rewrites, O, nothing)
    out === nothing || return out
    expr = Expr(:call, map)
    push!(expr.args, toexpr(op.f, st))
    for arg in arguments(O)
        push!(expr.args, toexpr(arg, st))
    end
    return expr
end

function function_to_expr(@nospecialize(op::SymbolicUtils.Mapreducer), O, st)
    out = get(st.rewrites, O, nothing)
    out === nothing || return out
    expr = Expr(:call, mapreduce)
    kws = Expr(:parameters)
    if op.dims isa Int
        push!(kws.args, Expr(:kw, :dims, op.dims))
    end
    if op.init !== nothing
        push!(kws.args, Expr(:kw, :init, toexpr(op.init, st)))
    end
    if !isempty(kws.args)
        push!(expr.args, kws)
    end
    push!(expr.args, op.f)
    push!(expr.args, op.reduce)
    for arg in arguments(O)
        push!(expr.args, toexpr(arg, st))
    end
    return expr
end

const ARRAY_OUTSYM = Symbol("_out")

function function_to_expr(::typeof(getindex), O::BasicSymbolic{T}, st) where {T}
    out = get(st.rewrites, O, nothing)
    out === nothing || return out

    args = arguments(O)
    if issym(args[1]) && nameof(args[1]) == IDXS_SYM
        @assert length(args) == 2
        return Symbol(:_, unwrap_const(args[2]))
    end
    args = map(Base.Fix2(toexpr, st), arguments(O))
    expr = Expr(:call, getindex)
    append!(expr.args, args)
    return expr
end

function function_to_expr(::Type{ArrayOp{T}}, O::BasicSymbolic{T}, st) where {T}
    out = get(st.rewrites, O, nothing)
    out === nothing || return out

    # TODO: better infer default eltype from `O`
    output_eltype = get(st.rewrites, :arrayop_eltype, Float64)
    delete!(st.rewrites, :arrayop_eltype)
    sh = shape(O)
    default_output_buffer = if is_array_shape(sh)
        term(zeros, output_eltype, size(O))
    else
        term(zero, output_eltype)
    end
    output_buffer = get(st.rewrites, :arrayop_output, default_output_buffer)
    delete!(st.rewrites, :arrayop_output)
    return toexpr(
        Let(
            [
                Assignment(ARRAY_OUTSYM, output_buffer),
            ], Let([Assignment(Symbol("%$ARRAY_OUTSYM"), inplace_expr(O, ARRAY_OUTSYM))], ARRAY_OUTSYM, false),
            true
        ), st
    )
end

function unidealize_indices(expr::BasicSymbolic{T}, ranges, new_ranges) where {T}
    iscall(expr) || return expr
    op = operation(expr)
    args = arguments(expr)
    if op !== getindex
        for i in eachindex(args)
            arg = unidealize_indices(args[i], ranges, new_ranges)
            isequal(arg, args[i]) && continue
            if args isa ROArgsT
                args = copy(parent(args))
            end
            args[i] = arg
        end
        args isa ROArgsT && return expr
        return maketerm(typeof(expr), op, args, nothing)
    end

    arr = first(args)
    sh = shape(arr)
    sh isa Unknown && return expr
    sh = sh::ShapeVecT

    for i in eachindex(sh)
        ax = sh[i]
        idx = args[i + 1]
        vars = Set{BasicSymbolic{T}}()
        search_variables!(vars, idx; is_atomic = _is_index_variable)
        length(vars) == 1 || continue
        idxvar = only(vars)
        haskey(ranges, idxvar) && continue
        new_ranges[idxvar] = 1:length(ax)
        first(ax) == 1 && continue

        if args isa ROArgsT
            args = copy(parent(args))
        end
        args[i + 1] = idx - (first(ax) - 1)
    end
    args isa ROArgsT && return expr
    return maketerm(typeof(expr), getindex, args, nothing)
end

function inplace_expr(x::BasicSymbolic{T}, outsym) where {T}
    # TODO:
    # if x.term !== nothing
    #     ex = inplace_builtin(x.term, outsym)
    #     if ex !== nothing
    #         return ex
    #     end
    # end
    if outsym isa Symbol
        outsym = Sym{T}(outsym; type = Any, shape = Unknown(-1))
    end
    sh = shape(x)
    ranges = x.ranges
    new_ranges = RangesT{T}()
    new_expr = unidealize_indices(x.expr, ranges, new_ranges)
    loopvar_order = unique!(filter(x -> x isa BasicSymbolic{T}, vcat(reverse(x.output_idx), collect(keys(ranges)), collect(keys(new_ranges)))))

    if is_array_shape(sh)
        inner_expr = SetArray(false, outsym, [AtIndex(term(CartesianIndex, x.output_idx...), term(x.reduce, term(getindex, outsym, x.output_idx...), new_expr))])
    else
        inner_expr = Assignment(outsym, term(x.reduce, outsym, new_expr))
    end
    merge!(new_ranges, ranges)
    loops = foldl(reverse(loopvar_order), init=inner_expr) do acc, k
        ForLoop(k, new_ranges[k], acc)
    end

    return loops
end

function function_to_expr(::Type{ArrayMaker{T}}, O::BasicSymbolic{T}, st) where {T}
    out = get(st.rewrites, O, nothing)
    out === nothing || return out

    # TODO: better infer default eltype from `O`
    output_eltype = get(st.rewrites, :arraymaker_eltype, Float64)
    delete!(st.rewrites, :arraymaker_eltype)
    sh = shape(O)
    default_output_buffer = term(zeros, output_eltype, size(O))
    output_buffer = get(st.rewrites, :arraymaker_output, default_output_buffer)
    delete!(st.rewrites, :arraymaker_output)
    ir = Assignment[]
    regions, values = @match O begin
        BSImpl.ArrayMaker(; regions, values) => (regions, values)
    end
    @union_split_smallvec regions @union_split_smallvec values begin
        for (region, val) in zip(regions, values)
            args = ArgsT{T}((ARRAY_OUTSYM,))
            # `append!`  doesn't convert on 1.10
            @union_split_smallvec region for reg in region
                push!(args, BSImpl.Const{T}(reg))
            end
            vw = BSImpl.Term{T}(view, args; type = Any)
            @match val begin
                BSImpl.ArrayOp(;) => begin
                    st.rewrites[:arrayop_output] = vw
                    push!(ir, Assignment(Symbol("__tmp_ₐ"), toexpr(val, st)))
                end
                BSImpl.ArrayMaker(;) => begin
                    st.rewrites[:arraymaker_output] = vw
                    push!(ir, Assignment(Symbol("__tmp_ₐ"), toexpr(val, st)))
                end
                _ => begin
                    push!(ir, Assignment(Symbol("__tmp_ₐ"), :($copyto!($view($ARRAY_OUTSYM, $(region...)), $(toexpr(val, st))))))
                end
            end
        end
    end
    return toexpr(Let([Assignment(ARRAY_OUTSYM, output_buffer)], Let(ir, ARRAY_OUTSYM, false), true), st)
end

function function_to_expr(@nospecialize(op::Union{typeof(*),typeof(+)}), O, st)
    out = get(st.rewrites, O, nothing)
    out === nothing || return out
    if get(st.rewrites, :sort_addmul, true)::Bool
        args = parent(sorted_arguments(O))
    else
        args = parent(arguments(O))
    end

    if length(args) == 1
        return Expr(:call, op, toexpr(args[1], st))
    end
    if symtype(O) <: Number
        cur = Expr(:call, op, toexpr(args[1], st), toexpr(args[2], st))
        for i in 3:length(args)
            cur = Expr(:call, op, cur, toexpr(args[i], st))
        end
        return cur
    else
        expr = Expr(:call, op)
        @union_split_smallvec args for arg in args
            push!(expr.args, toexpr(arg, st))
        end
        return expr
    end
end

function function_to_expr(op::typeof(^), O::BasicSymbolic{T}, st) where {T}
    base, exp = arguments(O)
    base = toexpr(base, st)
    @match exp begin
        BSImpl.Const(; val) => begin
            if val isa Real
                if _isone(val)
                    return toexpr(base, st)
                end
                if _isone(-val)
                    return Expr(:call, inv, base)
                end
                if (val < 0)::Bool
                    val = -val
                    base = Expr(:call, inv, base)
                end
                if !(val isa Integer) && get(st.rewrites, :nanmath, false)::Bool
                    op = NaNMath.pow
                end
            end
            return Expr(:call, op, base, val)
        end
        _ => begin
            sT = symtype(exp)
            if get(st.rewrites, :nanmath, false)::Bool
                return Expr(:call, NaNMath.pow, base, toexpr(exp, st))
            else
                return Expr(:call, ^, base, toexpr(exp, st))
            end
        end
    end
end

function function_to_expr(::typeof(ifelse), O, st)
    args = arguments(O)
    return Expr(:if, toexpr(args[1], st), toexpr(args[2], st), toexpr(args[3], st))
end

toexpr(O::Expr, st) = O

function substitute_name(O, st)
    if (issym(O) || iscall(O)) && haskey(st.rewrites, O)
        st.rewrites[O]
    else
        O
    end
end

function toexpr(O, st)
    u = unwrap(O)
    if u !== O
        return toexpr(u, st)
    elseif _is_array_of_symbolics(O)
        return issparse(O) ? toexpr(MakeSparseArray(O), st) : toexpr(MakeArray(O, typeof(O)), st)
    else
        return O
    end
end

function toexpr(O::BasicSymbolic{T}, st) where {T}
    if haskey(st.rewrites, O)
        O = st.rewrites[O]
        if !(O isa BasicSymbolic{T})
            return manual_dispatch_toexpr(O, st)
        end
    end
    O = O::BasicSymbolic{T}
    @match O begin
        BSImpl.Const(; val) => if val isa CodegenPrimitive
            return manual_dispatch_toexpr(val, st)
        else
            return val
        end
        BSImpl.Sym(; name) => return name
        BSImpl.ArrayOp(; term) => if term isa BasicSymbolic{T}
            return toexpr(term, st)
        else
            return function_to_expr(ArrayOp{T}, O, st)
        end
        BSImpl.ArrayMaker(;) => return function_to_expr(ArrayMaker{T}, O, st)
        BSImpl.Term(; f) => begin
            if f === (^)
                return function_to_expr((^), O, st)
            elseif f === ifelse
                return function_to_expr(ifelse, O, st)
            else
                return function_to_expr(f, O, st)
            end
        end
        BSImpl.Div(; num, den) => begin
            return Expr(:call, /, toexpr(num, st), toexpr(den, st))
        end
        BSImpl.AddMul(; variant) => if variant === AddMulVariant.ADD
            return function_to_expr((+), O, st)
        else
            return function_to_expr((*), O, st)
        end
    end
end

# Call elements of vector arguments by their name.
@matchable struct DestructuredArgs <: CodegenPrimitive
    elems
    inds
    name
    inbounds::Bool
    create_bindings::Bool
end

function DestructuredArgs(elems, name=nothing; inds=eachindex(elems), inbounds=false, create_bindings=true)
    if name === nothing
        # I'm sorry if you get a hash collision here lol
        name = Symbol("##arg#", hash((elems, inds, inbounds, create_bindings)))
    end
    DestructuredArgs(elems, inds, name, inbounds, create_bindings)
end

"""
    DestructuredArgs(elems, [name=gensym("arg")])

`elems` is a vector of symbols or call expressions.  When it appears as an argument in
`Func`, it expects a vector of the same length and de-structures the vector into its named
components. See example in `Func` for more information.

`name` is the name to be used for the argument in the generated function Expr.
"""
DestructuredArgs

function search_variables!(buffer, dargs::DestructuredArgs; kw...)
    elems = dargs.elems
    if elems isa Vector{BasicSymbolic{SymReal}}
        search_variables!(buffer, elems; kw...)
    elseif elems isa Vector{BasicSymbolic{SafeReal}}
        search_variables!(buffer, elems; kw...)
    elseif elems isa Vector{BasicSymbolic{TreeReal}}
        search_variables!(buffer, elems; kw...)
    else
        search_variables!(buffer, elems; kw...)
    end
end

toexpr(x::DestructuredArgs, st) = toexpr(x.name, st)
get_rewrites(args::DestructuredArgs) = []
function get_rewrites(args::Union{AbstractArray, Tuple})
    rws = []
    for arg in args
        append!(rws, get_rewrites(arg))
    end
    return rws
end
get_rewrites(x) = []
get_rewrites(x::BasicSymbolic) = iscall(x) ? Any[x] : []

# Used in Symbolics
Base.@deprecate_binding get_symbolify get_rewrites

function get_assignments(d::DestructuredArgs, st)
    name = manual_dispatch_toexpr(d, st)
    assigns = Assignment[]
    for i in 1:(length(d.inds)::Int)
        idx = d.inds[i]
        if idx isa Symbol
            ex = Expr(:., name, QuoteNode(idx))
        else
            ex = Expr(:ref, name, idx)
        end
        if d.inbounds && d.create_bindings
            ex = Expr(:macrocall, Symbol("@inbounds"), LineNumberNode(0), ex)
        end
        push!(assigns, Assignment(d.elems[i], ex))
    end
    return assigns
end

@matchable struct Let <: CodegenPrimitive
    pairs::Vector{Union{Assignment,DestructuredArgs}} # an iterator of pairs, ordered
    body
    let_block::Bool
end

"""
    Let(assignments, body[, let_block])

A Let block.

- `assignments` is a vector of `Assignment`s
- `body` is the body of the let block
- `let_block` boolean (default=true) -- do not create a let block if false.
"""
Let(assignments, body) = Let(assignments, body, true)

function search_variables!(buffer, l::Let; kw...)
    lhsbuf = empty(buffer)
    rhsbuf = empty(buffer)
    for elem in l.pairs
        if elem isa Assignment
            lhs = elem.lhs
            rhs = elem.rhs
            if lhs isa BasicSymbolic{SymReal}
                search_variables!(lhsbuf, lhs; kw...)
            elseif lhs isa BasicSymbolic{SafeReal}
                search_variables!(lhsbuf, lhs; kw...)
            elseif lhs isa BasicSymbolic{TreeReal}
                search_variables!(lhsbuf, lhs; kw...)
            elseif lhs isa Symbol
            else
                search_variables!(lhsbuf, lhs; kw...)
            end
            if rhs isa BasicSymbolic{SymReal}
                search_variables!(rhsbuf, rhs; kw...)
            elseif rhs isa BasicSymbolic{SafeReal}
                search_variables!(rhsbuf, rhs; kw...)
            elseif rhs isa BasicSymbolic{TreeReal}
                search_variables!(rhsbuf, rhs; kw...)
            elseif rhs isa Vector{BasicSymbolic{SymReal}}
                search_variables!(rhsbuf, rhs; kw...)
            elseif rhs isa Vector{BasicSymbolic{SafeReal}}
                search_variables!(rhsbuf, rhs; kw...)
            elseif rhs isa Vector{BasicSymbolic{TreeReal}}
                search_variables!(rhsbuf, rhs; kw...)
            elseif rhs isa Matrix{BasicSymbolic{SymReal}}
                search_variables!(rhsbuf, rhs; kw...)
            elseif rhs isa Matrix{BasicSymbolic{SafeReal}}
                search_variables!(rhsbuf, rhs; kw...)
            elseif rhs isa Matrix{BasicSymbolic{TreeReal}}
                search_variables!(rhsbuf, rhs; kw...)
            elseif rhs isa Symbol
            else
                search_variables!(rhsbuf, rhs; kw...)
            end
        else
            search_variables!(rhsbuf, elem; kw...)
        end
    end
    setdiff!(rhsbuf, lhsbuf)
    union!(buffer, rhsbuf)
end

function handle_let_pair!(dargs::Vector{Assignment}, @nospecialize(x::Union{DestructuredArgs, Assignment}), st)
    if x isa DestructuredArgs
        if x.create_bindings
            for a in get_assignments(x, st)
                handle_let_pair!(dargs, a, st)
            end
        else
            for a in get_assignments(x, st)
                st.rewrites[a.lhs] = a.rhs
            end
        end
    elseif x isa Assignment
        lhs = x.lhs
        if lhs isa DestructuredArgs
            if lhs.create_bindings
                handle_let_pair!(dargs, Assignment(lhs.name, x.rhs), st)
                for a in get_assignments(lhs, st)
                    handle_let_pair!(dargs, a, st)
                end
            else
                handle_let_pair!(dargs, Assignment(lhs.name, x.rhs), st)
                for a in get_assignments(lhs, st)
                    st.rewrites[a.lhs] = a.rhs
                end
            end
        else
            push!(dargs, x)
        end
    else
        _unreachable()
    end
end

function toexpr(l::Let, st)
    if all(x->x isa Assignment && !(x.lhs isa DestructuredArgs), l.pairs)
        dargs = Vector{Assignment}(l.pairs)
    else
        dargs = Assignment[]
        for x in l.pairs
            handle_let_pair!(dargs, x, st)
        end
    end

    bindings = Expr(:block)
    for asg in dargs
        union_rewrites!(st.rewrites, get_rewrites(asg.lhs))
        push!(bindings.args, toexpr(asg, st))
    end

    if l.let_block
        return Expr(:let, bindings, manual_dispatch_toexpr(l.body, st))
    end
    isempty(bindings.args) && return manual_dispatch_toexpr(l.body, st)
    push!(bindings.args, manual_dispatch_toexpr(l.body, st))
    return bindings
end

@matchable struct Func <: CodegenPrimitive
    args::Vector{Any}
    kwargs::Vector{Assignment}
    body
    pre::Vector{Any}
end

function search_variables!(buffer, f::Func; kw...)
    search_variables!(buffer, f.args; kw...)
    search_variables!(buffer, f.kwargs; kw...)
    body = f.body
    if body isa BasicSymbolic{SymReal}
        search_variables!(buffer, body; kw...)
    elseif body isa BasicSymbolic{SafeReal}
        search_variables!(buffer, body; kw...)
    elseif body isa BasicSymbolic{TreeReal}
        search_variables!(buffer, body; kw...)
    elseif body isa Vector{BasicSymbolic{SymReal}}
        search_variables!(buffer, body; kw...)
    elseif body isa Vector{BasicSymbolic{SafeReal}}
        search_variables!(buffer, body; kw...)
    elseif body isa Vector{BasicSymbolic{TreeReal}}
        search_variables!(buffer, body; kw...)
    elseif body isa Matrix{BasicSymbolic{SymReal}}
        search_variables!(buffer, body; kw...)
    elseif body isa Matrix{BasicSymbolic{SafeReal}}
        search_variables!(buffer, body; kw...)
    elseif body isa Matrix{BasicSymbolic{TreeReal}}
        search_variables!(buffer, body; kw...)
    elseif body isa Let
        search_variables!(buffer, body; kw...)
    elseif body isa Symbol
    else
        search_variables!(buffer, body; kw...)
    end
end

Func(args, kwargs, body) = Func(args, kwargs, body, Assignment[])

"""
    Func(args, kwargs, body[, pre])

A function.

- `args` is a vector of expressions
- `kwargs` is a vector of `Assignment`s
- `body` is the body of the function
- `pre` a vector of expressions to be prepended to the function body,
   for example, it could be `[Expr(:meta, :inline), Expr(:meta, :propagate_inbounds)]`
   to create an `@inline @propagate_inbounds` function definition.

**Special features in `args`**:

- args can contain `DestructuredArgs`
- call expressions

For example,

```julia-repl
julia> @syms a b c t f(d) x(t) y(t) z(t)
(a, b, c, t, f(::Number)::Number, x(::Number)::Number, y(::Number)::Number, z(::Number)::Number)

julia> func = Func([a,x(t), DestructuredArgs([b, y(t)]), f], # args
                   [c ← 2, z(t) ← 42], # kwargs
                   f((a + b + c) / x(t) + y(t) + z(t)));

julia> toexpr(func)
:(function (a, var"x(t)", var"##arg#255", f; c = 2, var"z(t)" = 42)
      let b = var"##arg#255"[1], var"y(t)" = var"##arg#255"[2]
          f((+)(var"y(t)", var"z(t)", (*)((+)(a, b, c), (inv)(var"x(t)"))))
      end
  end)
```

- the second argument is a `DestructuredArgs`, in the `Expr` form, it is given a random name, and is expected to receive a vector or tuple of size 2 containing the values of `b` and `y(t)`. The let block that is automatically generated "destructures" these arguments.
- `x(t)` and `y(t)` have been replaced with `var"x(t)"` and `var"y(t)"` symbols throughout
  the generated Expr. This makes sure that we are not actually calling the expressions `x(t)` or `y(t)` but instead passing the right values in place of the whole expression.
- `f` is also a function-like symbol, same as `x` and `y`, but since the `args` array contains `f` as itself rather than as say, `f(t)`, it does not become a `var"f(t)"`. The generated function expects a function of one argument to be passed in the position of `f`.

An example invocation of this function is:

```julia-repl
julia> executable = eval(toexpr(func))
#10 (generic function with 1 method)

julia> executable(1, 2.0, [2,3.0], x->string(x); var"z(t)" = sqrt(42))
"11.98074069840786"
```
"""
Func

toexpr_kw(f, st) = Expr(:kw, toexpr(f, st).args...)

function toexpr(f::Func, st)
    for arg in f.args
        union_rewrites!(st.rewrites, get_rewrites(arg))
    end
    for arg in f.kwargs
        union_rewrites!(st.rewrites, get_rewrites(arg.lhs))
    end
    dargs = Union{Assignment, DestructuredArgs}[]
    for arg in f.args
        if arg isa DestructuredArgs
            push!(dargs, arg)
        end
    end
    body = manual_dispatch_toexpr(Let(dargs, f.body, false), st)
    fn_args = Expr(:tuple)
    if !isempty(f.kwargs)
        fn_kws = Expr(:parameters)
        for asg in f.kwargs
            asg_expr = toexpr(asg, st)
            push!(fn_kws.args, Expr(:kw, asg_expr.args[1], asg_expr.args[2]))
        end
        push!(fn_args.args, fn_kws)
    end
    for arg in f.args
        push!(fn_args.args, manual_dispatch_toexpr(arg, st))
    end
    fn_body = Expr(:block)
    append!(fn_body.args, f.pre)
    push!(fn_body.args, body)
    return Expr(:function, fn_args, fn_body)
end

@matchable struct SetArray <: CodegenPrimitive
    inbounds::Bool
    arr
    elems  # Either iterator of Pairs or just an iterator
    return_arr::Bool
end

"""
    SetArray(inbounds::Bool, arr, elems[, return_arr::Bool])

An expression representing setting of elements of `arr`.

By default, every element of `elems` is copied over to `arr`,

but if `elems` contains `AtIndex(i, val)` objects, then `arr[i] = val`
is performed in its place.

`inbounds` is a boolean flag, `true` surrounds the resulting expression
in an `@inbounds`.

`return_arr` is a flag which controls whether the generated `begin..end` block
returns the `arr`. Defaults to `false`, in which case the block returns `nothing`.
"""
SetArray

SetArray(inbounds, arr, elems) = SetArray(inbounds, arr, elems, false)

function search_variables!(buffer, sa::SetArray; kw...)
    body = sa.arr
    if body isa BasicSymbolic{SymReal}
        search_variables!(buffer, body; kw...)
    elseif body isa BasicSymbolic{SafeReal}
        search_variables!(buffer, body; kw...)
    elseif body isa BasicSymbolic{TreeReal}
        search_variables!(buffer, body; kw...)
    elseif body isa Symbol
    else
        search_variables!(buffer, body; kw...)
    end
    elems = sa.elems
    if elems isa Vector{AtIndex}
        search_variables!(buffer, elems; kw...)
    else
        search_variables!(buffer, elems; kw...)
    end
end

@matchable struct AtIndex <: CodegenPrimitive
    i
    elem
end

function search_variables!(buffer, ai::AtIndex; kw...)
    i = ai.i
    elem = ai.elem
    if i isa BasicSymbolic{SymReal}
        search_variables!(buffer, i; kw...)
    elseif i isa BasicSymbolic{SafeReal}
        search_variables!(buffer, i; kw...)
    elseif i isa BasicSymbolic{TreeReal}
        search_variables!(buffer, i; kw...)
    elseif i isa CartesianIndex
    elseif i isa Integer
    elseif i isa Symbol
    else
        search_variables!(buffer, i; kw...)
    end
    if elem isa BasicSymbolic{SymReal}
        search_variables!(buffer, elem; kw...)
    elseif elem isa BasicSymbolic{SafeReal}
        search_variables!(buffer, elem; kw...)
    elseif elem isa BasicSymbolic{TreeReal}
        search_variables!(buffer, elem; kw...)
    elseif elem isa Symbol
    else
        search_variables!(buffer, elem; kw...)
    end
end

function toexpr(a::AtIndex, st)
    toexpr(a.elem, st)
end

function toexpr(s::SetArray, st)
    ex = quote
        $([:($(toexpr(s.arr, st))[$(ex isa AtIndex ? toexpr(ex.i, st) : i)] = $(toexpr(ex, st)))
           for (i, ex) in enumerate(s.elems)]...)
        $(s.return_arr ? toexpr(s.arr, st) : nothing)
    end
    s.inbounds ? :(@inbounds $ex) : ex
end

@matchable struct MakeArray <: CodegenPrimitive
    elems
    similarto # Must be either a reference to an array or a concrete type
    output_eltype
end

function search_variables!(buffer, ma::MakeArray; kw...)
    elems = ma.elems
    if elems isa Vector{BasicSymbolic{SymReal}}
        search_variables!(buffer, elems; kw...)
    elseif elems isa Vector{BasicSymbolic{SafeReal}}
        search_variables!(buffer, elems; kw...)
    elseif elems isa Vector{BasicSymbolic{TreeReal}}
        search_variables!(buffer, elems; kw...)
    elseif elems isa Matrix{BasicSymbolic{SymReal}}
        search_variables!(buffer, elems; kw...)
    elseif elems isa Matrix{BasicSymbolic{SafeReal}}
        search_variables!(buffer, elems; kw...)
    elseif elems isa Matrix{BasicSymbolic{TreeReal}}
        search_variables!(buffer, elems; kw...)
    else
        search_variables!(buffer, elems; kw...)
    end
end

"""
    MakeArray(elems, similarto, [output_eltype=nothing])

An expression which constructs an array.

- `elems` is the output array
- `similarto` can either be a type, or some symbol that is an array whose type needs to
   be emulated. If `similarto` is a StaticArrays.SArray, then the output array is also
   created as an `SArray`, similarly, an `Array` will result in an `Array`, and a
   `LabelledArrays.SLArray` will result in a labelled static array.
- `output_eltype`: if set, then forces the element type of the output array to be this.
   by default, the output type is inferred automatically.

You can define:
```julia
@inline function create_array(A::Type{<:MyArray},a
                              ::Nothing, d::Val{dims}, elems...) where dims

# and

@inline function create_array(::Type{<:MyArray}, T, ::Val{dims}, elems...) where dims
```

which creates an array of size `dims` using the elements `elems` and eltype `T`, to allow
`MakeArray` to create arrays similarto `MyArray`s.

"""
MakeArray

MakeArray(elems, similarto) = MakeArray(elems, similarto, nothing)

function toexpr(a::MakeArray, st)
    similarto = toexpr(a.similarto, st)
    T = similarto isa Type ? similarto : :(typeof($similarto))
    ndim = ndims(a.elems)
    elT = a.output_eltype
    quote
        $create_array($T,
                     $elT,
                     Val{$ndim}(),
                     Val{$(size(a.elems))}(),
                     $(map(x->toexpr(x, st), a.elems)...),)
    end
end

## Array
@inline function _create_array(::Type{<:Array}, T, ::Val{dims}, elems...) where dims
    arr = Array{T}(undef, dims)
    @assert prod(dims) == nfields(elems)
    @inbounds for i=1:prod(dims)
        arr[i] = elems[i]
    end
    arr
end

@inline function create_array(A::Type{<:Array}, T, ::Val, d::Val, elems...)
    _create_array(A, T, d, elems...)
end

@inline function create_array(A::Type{<:Array}, ::Nothing, ::Val, d::Val{dims}, elems...) where dims
    T = promote_type(map(typeof, elems)...)
    _create_array(A, T, d, elems...)
end

## Vector
#
@inline function create_array(::Type{<:Array}, ::Nothing, ::Val{1}, ::Val{dims}, elems...) where dims
    [elems...]
end

@inline function create_array(::Type{<:Array}, T, ::Val{1}, ::Val{dims}, elems...) where dims
    T[elems...]
end

## Matrix

@inline function create_array(::Type{<:Array}, ::Nothing, ::Val{2}, ::Val{dims}, elems...) where dims
    vhcat(dims, elems...)
end

@inline function create_array(::Type{<:Array}, T, ::Val{2}, ::Val{dims}, elems...) where dims
    typed_vhcat(T, dims, elems...)
end

@inline function create_array(::Type{<:Base.ReinterpretArray}, ::Nothing,
        ::Val{1}, ::Val{dims}, elems...) where {dims}
    [elems...]
end

@inline function create_array(
        ::Type{<:Base.ReinterpretArray}, T, ::Val{1}, ::Val{dims}, elems...) where {dims}
    T[elems...]
end


vhcat(sz::Tuple{Int,Int}, xs::T...) where {T} = typed_vhcat(T, sz, xs...)
vhcat(sz::Tuple{Int,Int}, xs::Number...) = typed_vhcat(Base.promote_typeof(xs...), sz, xs...)
vhcat(sz::Tuple{Int,Int}, xs...) = typed_vhcat(Base.promote_eltypeof(xs...), sz, xs...)

function typed_vhcat(::Type{T}, sz::Tuple{Int, Int}, xs...) where T
    nr,nc = sz
    a = Matrix{T}(undef, nr, nc)
    k = 1
    for j=1:nc
        @inbounds for i=1:nr
            a[i, j] = xs[k]
            k += 1
        end
    end
    a
end

## Arrays of the special kind
@inline function create_array(A::Type{<:SubArray{T,N,P,I,L}}, S, nd::Val, d::Val, elems...) where {T,N,P,I,L}
    create_array(P, S, nd, d, elems...)
end

@inline function create_array(A::Type{<:PermutedDimsArray{T,N,perm,iperm,P}}, S, nd::Val, d::Val, elems...) where {T,N,perm,iperm,P}
    create_array(P, S, nd, d, elems...)
end


@inline function create_array(A::Type{<:Transpose{T,P}}, S, nd::Val, d::Val, elems...) where {T,P}
    create_array(P, S, nd, d, elems...)
end

@inline function create_array(A::Type{<:UpperTriangular{T,P}}, S, nd::Val, d::Val, elems...) where {T,P}
    create_array(P, S, nd, d, elems...)
end

## SArray
@inline function create_array(::Type{<:SArray}, ::Nothing, nd::Val, ::Val{dims}, elems...) where dims
    SArray{Tuple{dims...}}(elems)
end

@inline function create_array(::Type{<:SArray}, T, nd::Val, ::Val{dims}, elems...) where dims
    SArray{Tuple{dims...}, T}(elems)
end

## MArray
@inline function create_array(::Type{<:MArray}, ::Nothing, nd::Val, ::Val{dims}, elems...) where dims
    MArray{Tuple{dims...}}(elems)
end

@inline function create_array(::Type{<:MArray}, T, nd::Val, ::Val{dims}, elems...) where dims
    MArray{Tuple{dims...}, T}(elems)
end

## We use a separate type for Sparse Arrays to sidestep the need for
## iszero to be defined on the expression type
@matchable struct MakeSparseArray{S<:AbstractSparseArray} <: CodegenPrimitive
    array::S
end

function search_variables!(buffer, msa::MakeSparseArray; kw...)
    search_variables!(buffer, msa.array; kw...)
end

"""
    MakeSpaseArray(array)

An expression which creates a `SparseMatrixCSC` or a `SparseVector`.

The generated expression contains the sparsity information of `array`,

it only creates the `nzval` field at run time.
"""
MakeSparseArray

function toexpr(a::MakeSparseArray{<:SparseMatrixCSC}, st)
    sp = a.array
    :(SparseMatrixCSC($(sp.m), $(sp.n),
                      $(copy(sp.colptr)), $(copy(sp.rowval)),
                      [$(toexpr.(sp.nzval, (st,))...)]))
end

function toexpr(a::MakeSparseArray{<:SparseVector}, st)
    sp = a.array
    :(SparseVector($(sp.n),
                   $(copy(sp.nzind)),
                   [$(toexpr.(sp.nzval, (st,))...)]))
end

@matchable struct MakeTuple <: CodegenPrimitive
    elems
end

MakeTuple(x::Tuple) = MakeTuple(collect(x))

"""
    MakeTuple(tup)

Make a Tuple from a tuple of expressions.
"""
MakeTuple

function toexpr(a::MakeTuple, st)
    :(($(toexpr.(a.elems, (st,))...),))
end

"""
    Multithreaded

A parallelism type for `SpawnFetch` that uses Julia's threading system.

When used with `SpawnFetch{Multithreaded}`, expressions are executed
in parallel using `Threads.@spawn`.

# Examples
```julia
julia> SpawnFetch{Multithreaded}([func1, func2], combine_func)
```

See also: [`SpawnFetch`](@ref)
"""
struct Multithreaded end
"""
    SpawnFetch{ParallelType}(funcs [, args], reduce)

Run every expression in `funcs` in its own task, the expression
should be a `Func` object and is passed to `Threads.Task(f)`.
If `Func` takes arguments, then the arguments must be passed in as `args`--a vector of vector of arguments to each function in `funcs`. We don't use `@spawn` in order to support RuntimeGeneratedFunctions which disallow closures, instead we interpolate these functions or closures as smaller RuntimeGeneratedFunctions.

`reduce` function is used to combine the results of executing `exprs`. A SpawnFetch expression returns the reduced result.


Use `Symbolics.MultithreadedForm` ParallelType from the Symbolics.jl package to get the RuntimeGeneratedFunction version SpawnFetch.

`ParallelType` can be used to define more parallelism types
SymbolicUtils supports `Multithreaded` type. Which spawns
threaded tasks.
"""
struct SpawnFetch{Typ} <: CodegenPrimitive
    exprs::Vector
    args::Union{Nothing, Vector}
    combine
end

function search_variables!(buffer, sf::SpawnFetch; kw...)
    search_variables!(buffer, sf.exprs)
    search_variables!(buffer, sf.args)
end

(::Type{SpawnFetch{T}})(exprs, combine) where {T} = SpawnFetch{T}(exprs, nothing, combine)

function toexpr(p::SpawnFetch{Multithreaded}, st)
    args = p.args === nothing ? Iterators.repeated((), length(p.exprs)) : p.args
    spawns = map(p.exprs, args) do thunk, xs
        :(Base.Threads.@spawn $(toexpr(thunk, st))($(toexpr.(xs, (st,))...)))
    end
    quote
        $(toexpr(p.combine, st))(map(fetch, ($(spawns...),))...)
    end
end

"""
    LiteralExpr(ex)

Literally `ex`, an `Expr`. `toexpr` on `LiteralExpr` recursively calls
`toexpr` on any interpolated symbolic expressions.
"""
struct LiteralExpr <: CodegenPrimitive
    ex
end

recurse_expr(ex::Expr, st) = Expr(ex.head, recurse_expr.(ex.args, (st,))...)
recurse_expr(ex, st) = toexpr(ex, st)

function toexpr(exp::LiteralExpr, st)
    recurse_expr(exp.ex, st)
end

"""
    ForLoop(itervar, range, body)

Generate a `for` loop of the form
```julia
for itervar in range
    body
end
```
"""
struct ForLoop <: CodegenPrimitive
    itervar
    range
    body
end

function search_variables!(buffer, fl::ForLoop; kw...)
    itervar = fl.itervar
    range = fl.range
    body = fl.body

    if itervar isa BasicSymbolic{SymReal}
        search_variables!(buffer, itervar; kw...)
    elseif itervar isa BasicSymbolic{SafeReal}
        search_variables!(buffer, itervar; kw...)
    elseif itervar isa BasicSymbolic{TreeReal}
        search_variables!(buffer, itervar; kw...)
    elseif itervar isa Symbol
    else
        search_variables!(buffer, itervar; kw...)
    end

    if range isa BasicSymbolic{SymReal}
        search_variables!(buffer, range; kw...)
    elseif range isa BasicSymbolic{SafeReal}
        search_variables!(buffer, range; kw...)
    elseif range isa BasicSymbolic{TreeReal}
        search_variables!(buffer, range; kw...)
    elseif range isa Symbol
    else
        search_variables!(buffer, range; kw...)
    end

    if body isa BasicSymbolic{SymReal}
        search_variables!(buffer, body; kw...)
    elseif body isa BasicSymbolic{SafeReal}
        search_variables!(buffer, body; kw...)
    elseif body isa BasicSymbolic{TreeReal}
        search_variables!(buffer, body; kw...)
    elseif body isa Symbol
    else
        search_variables!(buffer, body; kw...)
    end
end

function toexpr(f::ForLoop, st)
    :(for $(toexpr(f.itervar, st)) in $(toexpr(f.range, st))
        $(toexpr(f.body, st))
    end)
end

### Code-related utilities

### Common subexprssion evaluation

const CSE_PREFIX = Vector{UInt8}("##cse#")

"""
    newsym!(state::CSEState, ::Type{T})

Generates new symbol of type `T` with unique name in `state`.
"""
@inline function newsym!(state, ::Type{T}, symtype::TypeT, sh::ShapeT) where {T <: SymVariant}
    @nospecialize symtype sh

    idx = state.varid[]
    state.varid[] += 1
    buffer = UInt8[]
    sizehint!(buffer, length(CSE_PREFIX) + ndigits(idx))
    append!(buffer, CSE_PREFIX)
    while idx > 0
        push!(buffer, '0' + (idx % 10))
        idx = div(idx, 10)
    end
    reverse!(@view(buffer[(length(CSE_PREFIX) + 1):end]))
    Sym{T}(Symbol(buffer); type = symtype, shape = sh)
end

"""
    $(TYPEDSIGNATURES)

Return `true` if CSE should descend inside `sym`, which has operation `f`.
"""
function cse_inside_expr(sym, f)
    return true
end

"""
    $(TYPEDEF)

A struct maintaining the state of CSE across multiple expressions. This allows
leveraging common subexpressions across a hierarchy of codegen constructs.

# Fields

$(TYPEDFIELDS)
"""
struct CSEState
    """
    An ordered list of assignment statements computing intermediate expressions
    for CSE. Also allows `DestructuredArgs` for `Let` CSE.
    """
    sorted_exprs::Vector{Union{Assignment, DestructuredArgs}}
    """
    A mapping of symbolic expression to the LHS in `sorted_exprs` that computes it.
    """
    visited::IdDict{SymbolicUtils.IDType, Union{BasicSymbolic{SymReal}, BasicSymbolic{SafeReal}, BasicSymbolic{TreeReal}}}
    """
    Integer counter, used to generate unique names for intermediate variables.
    """
    varid::Ref{Int}
end

CSEState() = CSEState(Union{Assignment, DestructuredArgs}[], IdDict(), Ref(1))

# the copy still references the same `varid` Ref to work in nested scopes
Base.copy(x::CSEState) = CSEState(copy(x.sorted_exprs), copy(x.visited), x.varid)

"""
    $(TYPEDSIGNATURES)

Return a `CSEState` for a new scope inside the one represented by `state`. The new
`CSEState` will use previously-CSEd bindings for expressions only involving variables
outside the new scope, but will generate new bindings for variables defined in this scope.
The new bindings will not affect the outer scope.
"""
function new_scope(state::CSEState)
    state = copy(state)
    empty!(state.sorted_exprs)
    return state
end

"""
$(SIGNATURES)

Perform a topological sort on a symbolic expression represented as a Directed Acyclic 
Graph (DAG).

This function takes a symbolic expression `graph` (potentially containing shared common 
sub-expressions) and returns an array of `Assignment` objects.  Each `Assignment` 
represents a node in the sorted order, assigning a fresh symbol to its corresponding 
expression. The order ensures that all dependencies of a node appear before the node itself 
in the array.

Hash consing is assumed, meaning that structurally identical expressions are represented by 
the same object in memory. This allows for efficient equality checks using `IdDict`.
"""
function topological_sort(graph)
    state = CSEState()
    cse!(graph, state)
    return state.sorted_exprs
end

"""
    $(TYPEDSIGNATURES)

Perform common subexpression elimination on an expression.

This optimization identifies repeated subexpressions and replaces them with
variables to avoid redundant computation.

# Arguments
- `expr`: The expression to optimize

# Returns
An optimized expression with common subexpressions eliminated

# Examples
```julia-repl
julia> expr = :(sin(x) + sin(x) * cos(y))
julia> cse(expr)  # sin(x) is computed only once
```
"""
function cse(expr)
    state = CSEState()
    newexpr = cse!(expr, state)
    return apply_cse(newexpr, state)
end

"""
    $(TYPEDSIGNATURES)

Given a CSEd expression `newexpr` and the corresponding `state`, return an equivalent
expression with optimized computation.

This is also used when introducing new scopes in subexpressions.
"""
function apply_cse(newexpr, state::CSEState)
    # we special-case an empty `sorted_exprs` because e.g. if `expr` is a `Func`, it will
    # introduce a new scope and not add bindings to `state`. We don't want to wrap it
    # in a `Let`.
    isempty(state.sorted_exprs) && return newexpr
    return Let(state.sorted_exprs, newexpr, false)
end

"""
    cse!(x, state::CSEState)

Perform CSE on `x`, updating `state` with the required assignments and returning the
modified `x`. The returned value should be computable given the assignments in `state`
and should have the same type as `x`.
"""
function cse! end

function cse!(expr::BasicSymbolic{T}, state::CSEState) where {T}
    cse_visitor = let expr = expr, state = state
        function _cse_visitor()
            @match expr begin
                BSImpl.Const(;) => begin
                    new_expr = expr
                    sym = newsym!(state, T, symtype(new_expr), shape(new_expr))
                    push!(state.sorted_exprs, sym ← new_expr)
                    return sym
                end
                BSImpl.Sym(;) => return expr
                BSImpl.ArrayOp(; term) => if term === nothing
                    sym = newsym!(state, T, symtype(expr), shape(expr))
                    push!(state.sorted_exprs, sym ← expr)
                    return sym
                else
                    return cse!(term, state)
                end
                BSImpl.ArrayMaker(; regions, values, type, shape) => begin
                    values = copy(parent(values))
                    for i in eachindex(values)
                        values[i] = cse!(values[i], state)::BasicSymbolic{T}
                    end
                    return BSImpl.ArrayMaker{T}(regions, values; type, shape)
                end
                _ => begin
                    op = operation(expr)
                    args = arguments(expr)
                    if op isa BasicSymbolic{T}
                        SymbolicUtils.is_function_symbolic(op) || return expr
                    end
                    cse_inside_expr(expr, op)::Bool || return expr
                    args = copy(parent(args))
                    for i in eachindex(args)
                        args[i] = cse!(args[i], state)::BasicSymbolic{T}
                    end
                    # use `term` instead of `maketerm` because we only care about the operation being performed
                    # and not the representation. This avoids issues with `newsym` symbols not having sizes, etc.
                    new_expr = Term{T}(op, args; type = symtype(expr), shape = shape(expr))
                    sym = newsym!(state, T, symtype(expr), shape(expr))
                    push!(state.sorted_exprs, sym ← new_expr)
                    return sym
                end
            end
        end
    end
    return get!(cse_visitor, state.visited, expr.id)::BasicSymbolic{T}
end

cse!(x, ::CSEState) = x
cse!(x::Expr, ::CSEState) = x
cse!(x::LiteralExpr, ::CSEState) = x

cse!(x::CodegenPrimitive, state::CSEState) = throw(MethodError(cse!, (x, state)))

cse!(x::AbstractRange, ::CSEState) = x
function cse!(x::AbstractArray, state::CSEState)
    ux = SymbolicUtils.unwrap(x)
    if ux !== x
        return cse!(ux, state)
    end
    res = map(Base.Fix2(cse!, state), x)
    return res
end

function cse!(x::AbstractSparseArray, state::CSEState)
    I, J, V = findnz(x)
    V = map(Base.Fix2(cse!, state), V)
    return SparseArrays.sparse(I, J, V, size(x)...)
end

function cse!(x::Tuple, state::CSEState)
    res = map(Base.Fix2(cse!, state), x)
    return res
end

function cse!(x::MakeArray, state::CSEState)
    elems = x.elems
    if elems isa Vector{BasicSymbolic{SymReal}}
        return MakeArray(cse!(elems, state), x.similarto, x.output_eltype)
    elseif elems isa Matrix{BasicSymbolic{SymReal}}
        return MakeArray(cse!(elems, state), x.similarto, x.output_eltype)
    else
        return MakeArray(cse!(elems, state), x.similarto, x.output_eltype)
    end
end

function cse!(x::SetArray, state::CSEState)
    elems = x.elems
    if elems isa Vector{BasicSymbolic{SymReal}}
        return SetArray(x.inbounds, x.arr, cse!(elems, state), x.return_arr)
    elseif elems isa Matrix{BasicSymbolic{SymReal}}
        return SetArray(x.inbounds, x.arr, cse!(elems, state), x.return_arr)
    elseif elems isa Vector{AtIndex}
        return SetArray(x.inbounds, x.arr, cse!(elems, state), x.return_arr)
    elseif elems isa Matrix{AtIndex}
        return SetArray(x.inbounds, x.arr, cse!(elems, state), x.return_arr)
    else
        return SetArray(x.inbounds, x.arr, cse!(elems, state), x.return_arr)
    end
end

function cse!(x::MakeSparseArray, state::CSEState)
    arr = x.array
    if arr isa SparseMatrixCSC{BasicSymbolic{SymReal}, Int}
        return MakeSparseArray(cse!(arr, state))
    else
        return MakeSparseArray(cse!(arr, state))
    end
end

function cse!(x::Assignment, state::CSEState)
    lhs = x.lhs
    rhs = x.rhs
    if rhs isa BasicSymbolic{SymReal}
        result = Assignment(lhs, cse!(rhs, state))
    elseif rhs isa Vector{BasicSymbolic{SymReal}}
        result = Assignment(lhs, cse!(rhs, state))
    elseif rhs isa Matrix{BasicSymbolic{SymReal}}
        result = Assignment(lhs, cse!(rhs, state))
    elseif rhs isa Let
        result = Assignment(lhs, cse!(rhs, state))
    elseif rhs isa MakeArray
        result = Assignment(lhs, cse!(rhs, state))
    elseif rhs isa SetArray
        result = Assignment(lhs, cse!(rhs, state))
    else
        result = Assignment(lhs, cse!(rhs, state))
    end
    if lhs isa BasicSymbolic{SymReal}
        state.visited[lhs.id] = lhs
    elseif lhs isa BasicSymbolic{SafeReal}
        state.visited[lhs.id] = lhs
    elseif lhs isa BasicSymbolic{TreeReal}
        state.visited[lhs.id] = lhs
    end
    return result
end

function cse!(x::DestructuredArgs, state::CSEState)
    name = x.name
    if name isa BasicSymbolic{SymReal}
        return DestructuredArgs(x.elems, x.inds, cse!(name, state), x.inbounds, x.create_bindings)
    elseif name isa BasicSymbolic{SafeReal}
        return DestructuredArgs(x.elems, x.inds, cse!(name, state), x.inbounds, x.create_bindings)
    elseif name isa BasicSymbolic{TreeReal}
        return DestructuredArgs(x.elems, x.inds, cse!(name, state), x.inbounds, x.create_bindings)
    elseif name isa Symbol
        return DestructuredArgs(x.elems, x.inds, cse!(name, state), x.inbounds, x.create_bindings)
    elseif name isa Expr
        return DestructuredArgs(x.elems, x.inds, cse!(name, state), x.inbounds, x.create_bindings)
    else
        return DestructuredArgs(x.elems, x.inds, cse!(name, state), x.inbounds, x.create_bindings)
    end
end

function cse!(x::Let, state::CSEState)
    state = new_scope(state)
    # `Let` introduces a new scope. For each assignment `p` in `x.pairs`, we CSE it
    # and then append it to the new assignments from CSE. This is because the assignments
    # are imperative, so the CSE assignments for a given `p` can include previous `p`,
    # preventing us from simply wrapping the `Let` in another `Let`.
    for p in x.pairs
        if p isa Assignment
            push!(state.sorted_exprs, cse!(p, state))
        elseif p isa DestructuredArgs
            push!(state.sorted_exprs, cse!(p, state))
        else
            _unreachable()
        end
    end
    body = x.body
    if body isa BasicSymbolic{SymReal}
        return Let(state.sorted_exprs, cse!(body, state), x.let_block)
    elseif body isa BasicSymbolic{SafeReal}
        return Let(state.sorted_exprs, cse!(body, state), x.let_block)
    elseif body isa BasicSymbolic{TreeReal}
        return Let(state.sorted_exprs, cse!(body, state), x.let_block)
    elseif body isa Vector{BasicSymbolic{SymReal}}
        return Let(state.sorted_exprs, cse!(body, state), x.let_block)
    elseif body isa Matrix{BasicSymbolic{SymReal}}
        return Let(state.sorted_exprs, cse!(body, state), x.let_block)
    elseif body isa Let
        return Let(state.sorted_exprs, cse!(body, state), x.let_block)
    elseif body isa MakeArray
        return Let(state.sorted_exprs, cse!(body, state), x.let_block)
    elseif body isa ForLoop
        return Let(state.sorted_exprs, cse!(body, state), x.let_block)
    elseif body isa Symbol
        return Let(state.sorted_exprs, cse!(body, state), x.let_block)
    elseif body isa Expr
        return Let(state.sorted_exprs, cse!(body, state), x.let_block)
    elseif body isa Nothing
        return Let(state.sorted_exprs, cse!(body, state), x.let_block)
    else
        return Let(state.sorted_exprs, cse!(body, state), x.let_block)
    end
end

function cse!(x::Func, state::CSEState)
    state = new_scope(state)
    body = x.body
    if body isa BasicSymbolic{SymReal}
        return Func(x.args, x.kwargs, apply_cse(cse!(body, state), state), x.pre)
    elseif body isa BasicSymbolic{SafeReal}
        return Func(x.args, x.kwargs, apply_cse(cse!(body, state), state), x.pre)
    elseif body isa BasicSymbolic{TreeReal}
        return Func(x.args, x.kwargs, apply_cse(cse!(body, state), state), x.pre)
    elseif body isa Vector{BasicSymbolic{SymReal}}
        return Func(x.args, x.kwargs, apply_cse(cse!(body, state), state), x.pre)
    elseif body isa Matrix{BasicSymbolic{SymReal}}
        return Func(x.args, x.kwargs, apply_cse(cse!(body, state), state), x.pre)
    elseif body isa Let
        return Func(x.args, x.kwargs, apply_cse(cse!(body, state), state), x.pre)
    elseif body isa MakeArray
        return Func(x.args, x.kwargs, apply_cse(cse!(body, state), state), x.pre)
    elseif body isa ForLoop
        return Func(x.args, x.kwargs, apply_cse(cse!(body, state), state), x.pre)
    elseif body isa Symbol
        return Func(x.args, x.kwargs, apply_cse(cse!(body, state), state), x.pre)
    elseif body isa Expr
        return Func(x.args, x.kwargs, apply_cse(cse!(body, state), state), x.pre)
    elseif body isa Nothing
        return Func(x.args, x.kwargs, apply_cse(cse!(body, state), state), x.pre)
    else
        return Func(x.args, x.kwargs, apply_cse(cse!(body, state), state), x.pre)
    end
end

function cse!(x::AtIndex, state::CSEState)
    return AtIndex(cse!(x.i, state), cse!(x.elem, state))
end

function cse!(x::MakeTuple, state::CSEState)
    return MakeTuple(cse!(x.elems, state))
end

function cse!(x::SpawnFetch{T}, state::CSEState) where {T}
    # SpawnFetch is special. We want to CSE the individual functions independently, since
    # they shouldn't refer to global state. The arguments use `state`.
    return SpawnFetch{T}(map(cse, x.exprs), cse!(x.args, state), x.combine)
end

function cse!(x::ForLoop, state::CSEState)
    # cse the range with current scope, CSE the body with a new scope
    new_state = new_scope(state)
    return ForLoop(x.itervar, cse!(x.range, state), apply_cse(cse!(x.body, new_state), new_state))
end

"""
    OptimizationRule(name, detector, transformer, priority)

Defines an optimization rule with:
- `name`: A string identifier for the optimization.
- `detector`: A function that detects patterns in the IR. 
- `transformer`: A function that transforms the IR based on detected patterns, and returns updated IR
- `priority`: Integer priority (higher = applied first)

The detector function should implement the signature

```julia
detector(expr::Code.Let, state::Code.CSEState) -> Union{Nothing, Vector{<:AbstractMatched}}
```

Likewise, the transformer function should implement the signature

```julia
transformer(expr::Code.Let, match_data::Union{Nothing, Vector{<:AbstractMatched}}, state::Code.CSEState) -> Code.Let
```
"""
struct OptimizationRule{D, T}
    name::String
    detector::D
    transformer::T
    priority::Int
end

abstract type AbstractMatched end

function apply_substitution_map(expr::Code.Let, substitution_map::Dict)
    substitute_in_ir(expr, substitution_map)
end

function substitute_in_ir(s::Symbol, substitution_map::Dict)
    get(substitution_map, s, s)
end

function substitute_in_ir_base(s, substitution_map::Dict)
    if haskey(substitution_map, s)
        v = substitution_map[s]
        if issym(v)
            v
        else
            add_worker(vartype(first(v)), v)
        end
    else
        s
    end
end

function substitute_in_ir(expr, substitution_map::Dict)
    if iscall(expr)
        new_args = map(arguments(expr)) do arg
            substitute_in_ir(arg, substitution_map)
        end
        return Term{vartype(expr)}(operation(expr), new_args; type = symtype(expr))
    elseif issym(expr)
        substitute_in_ir_base(expr, substitution_map)
    else
        expr
    end
end

function substitute_in_ir(x::Code.Assignment, substitution_map::Dict)
    new_lhs = substitute_in_ir(Code.lhs(x), substitution_map)
    new_rhs = substitute_in_ir(Code.rhs(x), substitution_map)
    return Code.Assignment(new_lhs, new_rhs)
end

"""
    substitute_in_ir(expr::Code.Let, substitution_map::Dict) -> Code.Let

Recursively substitutes variables in the IR `expr` according to `substitution_map`.
"""
function substitute_in_ir(expr::Code.Let, substitution_map::Dict)
    isempty(substitution_map) && return expr

    new_pairs = map(expr.pairs) do p
        substitute_in_ir(p, substitution_map)
    end
    new_body = substitute_in_ir(expr.body, substitution_map)
    return Code.Let(new_pairs, new_body, expr.let_block)
end

Base.isempty(l::Code.Let) = isempty(l.pairs)   

# Apply optimization rules during CSE
function apply_optimization_rule(expr::Code.Let, state::Union{Code.CSEState, Code.LazyState}, rules::OptimizationRule)
    match_data = rules.detector(expr, state)
    if match_data !== nothing
        return rules.transformer(expr, match_data, state)
    end

    return expr
end
apply_optimization_rule(expr::Code.Let, state::Union{Code.CSEState, Code.LazyState}, rules::Nothing) = expr

function apply_optimization_rule(func::Code.Func, state, rule)
    Func(func.args, func.kwargs,
         apply_optimization_rule(func.body, state, rule),
         func.pre)
end

function apply_optimization_rules(expr, state, rules)
    isempty(rules) && return expr
    for rule in sort(rules, by = x -> x.priority)
        expr_new = apply_optimization_rule(expr, state, rule)
        expr = expr_new
    end

    expr
end

end
