module Code

using StaticArrays, SparseArrays, LinearAlgebra, NaNMath, SpecialFunctions,
      DocStringExtensions

export toexpr, Assignment, (←), Let, Func, DestructuredArgs, LiteralExpr,
       SetArray, MakeArray, MakeSparseArray, MakeTuple, AtIndex,
       SpawnFetch, Multithreaded, ForLoop, cse

import ..SymbolicUtils
import ..SymbolicUtils.Rewriters
import SymbolicUtils: @matchable, BasicSymbolic, Sym, Term, iscall, operation, arguments, issym,
                      symtype, sorted_arguments, metadata, isterm, term, maketerm, Symbolic, unwrap_const,
                      ArgsT, maybe_const
import SymbolicIndexingInterface: symbolic_type, NotSymbolic

##== state management ==##

struct NameState
    rewrites::Dict{Any, Any}
end
NameState() = NameState(Dict{Any, Any}())
function union_rewrites!(n, ts)
    for t in ts
        n[t] = Symbol(string(t))
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

"""
    toexpr(ex, [st,])

Convert a symbolic expression into an `Expr`, suitable to be passed into `eval`.

For example,

```julia
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

lhs(a::Assignment) = a.lhs
rhs(a::Assignment) = a.rhs

const (←) = Assignment

Base.convert(::Type{Assignment}, p::Pair) = Assignment(pair[1], pair[2])

toexpr(a::Assignment, st) = :($(toexpr(a.lhs, st)) = $(toexpr(a.rhs, st)))

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
function function_to_expr(op, O, st)
    (get(st.rewrites, :nanmath, false) && op in NaNMathFuns) || return nothing
    name = nameof(op)
    fun = GlobalRef(NaNMath, name)
    args = map(Base.Fix2(toexpr, st), arguments(O))
    expr = Expr(:call, fun)
    append!(expr.args, args)
    return expr
end

function function_to_expr(op::Union{typeof(*),typeof(+)}, O, st)
    out = get(st.rewrites, O, nothing)
    out === nothing || return out
    args = map(Base.Fix2(toexpr, st), sorted_arguments(O))
    if length(args) >= 3 && symtype(O) <: Number
        x, xs = Iterators.peel(args)
        foldl(xs, init=x) do a, b
            Expr(:call, op, a, b)
        end
    else
        expr = Expr(:call, op)
        append!(expr.args, args)
        expr
    end
end

function function_to_expr(op::typeof(^), O, st)
    base, exp = arguments(O)
    base = unwrap_const(base)
    exp = unwrap_const(exp)
    if exp isa Real && exp < 0
        base = Term(inv, ArgsT((base,)))
        if isone(-exp)
            return toexpr(base, st)
        else
            exp = -exp
        end
    end
    if get(st.rewrites, :nanmath, false) === true && !(exp isa Integer)
        op = NaNMath.pow
        return toexpr(Term(op, ArgsT((maybe_const(base), maybe_const(exp)))), st)
    end
    return nothing
end

function function_to_expr(::typeof(ifelse), O, st)
    args = arguments(O)
    :($(toexpr(args[1], st)) ? $(toexpr(args[2], st)) : $(toexpr(args[3], st)))
end

function function_to_expr(x::BasicSymbolic, O, st)
    issym(x) ? get(st.rewrites, O, nothing) : nothing
end

toexpr(O::Expr, st) = O

function substitute_name(O, st)
    if (issym(O) || iscall(O)) && haskey(st.rewrites, O)
        st.rewrites[O]
    else
        O
    end
end

function _is_tuple_or_array_of_symbolics(O)
    return O isa CodegenPrimitive ||
        (symbolic_type(O) != NotSymbolic() && !(O isa Union{Symbol, Expr})) ||
        _is_array_of_symbolics(O) ||
        _is_tuple_of_symbolics(O)
end

function _is_array_of_symbolics(O)
    # O is an array, not a symbolic array, and either has a non-symbolic eltype or contains elements that are
    # symbolic or arrays of symbolics
    return O isa AbstractArray && symbolic_type(O) == NotSymbolic() &&
        (symbolic_type(eltype(O)) != NotSymbolic() && !(eltype(O) <: Union{Symbol, Expr}) ||
        any(_is_tuple_or_array_of_symbolics, O))
end

# workaround for https://github.com/JuliaSparse/SparseArrays.jl/issues/599
function _is_array_of_symbolics(O::SparseMatrixCSC)
    return symbolic_type(eltype(O)) != NotSymbolic() && !(eltype(O) <: Union{Symbol, Expr}) ||
        any(_is_tuple_or_array_of_symbolics, findnz(O)[3])
end

function _is_tuple_of_symbolics(O::Tuple)
    return any(_is_tuple_or_array_of_symbolics, O)
end
_is_tuple_of_symbolics(O) = false

function toexpr(O, st)
    O = unwrap_const(O)
    O = substitute_name(O, st)
    if issym(O)
        return nameof(O)
    end

    if _is_array_of_symbolics(O)
        return issparse(O) ? toexpr(MakeSparseArray(O)) : toexpr(MakeArray(O, typeof(O)), st)
    end
    !iscall(O) && return O
    op = operation(O)
    expr′ = function_to_expr(op, O, st)
    if expr′ !== nothing
        return expr′
    else
        !iscall(O) && return O
        args = arguments(O)
        return Expr(:call, toexpr(op, st), map(x->toexpr(x, st), args)...)
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

toexpr(x::DestructuredArgs, st) = toexpr(x.name, st)
get_rewrites(args::DestructuredArgs) = ()
function get_rewrites(args::Union{AbstractArray, Tuple})
    cflatten(map(get_rewrites, args))
end
get_rewrites(x) = iscall(x) ? (x,) : ()
cflatten(x) = Iterators.flatten(x) |> collect

# Used in Symbolics
Base.@deprecate_binding get_symbolify get_rewrites

function get_assignments(d::DestructuredArgs, st)
    name = toexpr(d, st)
    map(d.inds, d.elems) do i, a
        ex = (i isa Symbol ? :($name.$i) : :($name[$i]))
        ex = d.inbounds && d.create_bindings ? :(@inbounds($ex)) : ex
        a ← ex
    end
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

function toexpr(l::Let, st)
    if all(x->x isa Assignment && !(x.lhs isa DestructuredArgs), l.pairs)
        dargs = l.pairs
    else
        assignments = []
        for x in l.pairs
            if x isa DestructuredArgs
                if x.create_bindings
                    append!(assignments, get_assignments(x, st))
                else
                    for a in get_assignments(x, st)
                        st.rewrites[a.lhs] = a.rhs
                    end
                end
            elseif x isa Assignment && x.lhs isa DestructuredArgs
                if x.lhs.create_bindings
                    push!(assignments, x.lhs.name ← x.rhs)
                    append!(assignments, get_assignments(x.lhs, st))
                else
                    push!(assignments, x.lhs.name ← x.rhs)
                    for a in get_assignments(x.lhs, st)
                        st.rewrites[a.lhs] = a.rhs
                    end
                end
            else
                push!(assignments, x)
            end
        end
        # expand and come back
        return toexpr(Let(assignments, l.body, l.let_block), st)
    end

    funkyargs = get_rewrites(map(lhs, dargs))
    union_rewrites!(st.rewrites, funkyargs)

    bindings = map(p->toexpr(p, st), dargs)
    l.let_block ? Expr(:let,
                       Expr(:block, bindings...),
                       toexpr(l.body, st)) : Expr(:block,
                                                  bindings...,
                                                  toexpr(l.body, st))
end

@matchable struct Func <: CodegenPrimitive
    args::Vector
    kwargs
    body
    pre::Vector
end

Func(args, kwargs, body) = Func(args, kwargs, body, [])

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

```julia

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

```julia
julia> executable = eval(toexpr(func))
#10 (generic function with 1 method)

julia> executable(1, 2.0, [2,3.0], x->string(x); var"z(t)" = sqrt(42))
"11.98074069840786"
```
"""
Func

toexpr_kw(f, st) = Expr(:kw, toexpr(f, st).args...)

function toexpr(f::Func, st)
    funkyargs = get_rewrites(vcat(f.args, map(lhs, f.kwargs)))
    union_rewrites!(st.rewrites, funkyargs)
    dargs = filter(x->x isa DestructuredArgs, f.args)
    if !isempty(dargs)
        body = Let(dargs, f.body, false)
    else
        body = f.body
    end
    if isempty(f.kwargs)
        :(function ($(map(x->toexpr(x, st), f.args)...),)
              $(f.pre...)
              $(toexpr(body, st))
          end)
    else
        :(function ($(map(x->toexpr(x, st), f.args)...),;
                    $(map(x->toexpr_kw(x, st), f.kwargs)...))
              $(f.pre...)
              $(toexpr(body, st))
          end)
    end
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

@matchable struct AtIndex <: CodegenPrimitive
    i
    elem
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
```
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
    SArray{Tuple{dims...}}(elems...)
end

@inline function create_array(::Type{<:SArray}, T, nd::Val, ::Val{dims}, elems...) where dims
    SArray{Tuple{dims...}, T}(elems...)
end

## MArray
@inline function create_array(::Type{<:MArray}, ::Nothing, nd::Val, ::Val{dims}, elems...) where dims
    MArray{Tuple{dims...}}(elems...)
end

@inline function create_array(::Type{<:MArray}, T, nd::Val, ::Val{dims}, elems...) where dims
    MArray{Tuple{dims...}, T}(elems...)
end

## We use a separate type for Sparse Arrays to sidestep the need for
## iszero to be defined on the expression type
@matchable struct MakeSparseArray{S<:AbstractSparseArray} <: CodegenPrimitive
    array::S
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

function toexpr(f::ForLoop, st)
    :(for $(toexpr(f.itervar, st)) in $(toexpr(f.range, st))
        $(toexpr(f.body, st))
    end)
end

### Code-related utilities

### Common subexprssion evaluation

"""
    newsym!(state::CSEState, ::Type{T})

Generates new symbol of type `T` with unique name in `state`.
"""
@inline function newsym!(state, ::Type{T}) where T 
    name = "##cse#$(state.varid[])"
    state.varid[] += 1
    Sym{T}(Symbol(name))
end

"""
    $(TYPEDSIGNATURES)

Return `true` if CSE should descend inside `sym`, which has operation `f` and
arguments `args...`.
"""
function cse_inside_expr(sym, f, args...)
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
    visited::IdDict{Union{SymbolicUtils.IDType, AbstractArray, Tuple}, BasicSymbolic}
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

Perform Common Subexpression Elimination on the given expression `expr`. Return an
equivalent `expr` with optimized computation.
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

indextype(::AbstractSparseArray{Tv, Ti}) where {Tv, Ti} = Ti


function cse!(expr::BasicSymbolic, state::CSEState)
    get!(state.visited, expr.id) do
        iscall(expr) || return expr

        op = operation(expr)
        args = arguments(expr)
        cse_inside_expr(expr, op, args...) || return expr
        args = map(args) do arg
            arg = unwrap_const(arg)
            if arg isa Union{Tuple, AbstractArray} &&
                (_is_array_of_symbolics(arg) || _is_tuple_of_symbolics(arg))
                if arg isa Tuple
                    new_arg = cse!(MakeTuple(arg), state)
                    sym = newsym!(state, Tuple{symtype.(arg)...})
                elseif issparse(arg)
                    new_arg = cse!(MakeSparseArray(arg), state)
                    sym = newsym!(state, AbstractSparseArray{symtype(eltype(arg)), indextype(arg), ndims(arg)})
                else
                    new_arg = cse!(MakeArray(arg, typeof(arg)), state)
                    sym = newsym!(state, AbstractArray{symtype(eltype(arg)), ndims(arg)})
                end
                push!(state.sorted_exprs, sym ← new_arg)
                state.visited[arg] = sym
                return sym
            end
            return cse!(arg, state)
        end
        # use `term` instead of `maketerm` because we only care about the operation being performed
        # and not the representation. This avoids issues with `newsym` symbols not having sizes, etc.
        new_expr = term(operation(expr), args...; type = symtype(expr))
        sym = newsym!(state, symtype(new_expr))
        push!(state.sorted_exprs, sym ← new_expr)
        return sym
    end
end

cse!(x, ::CSEState) = x
cse!(x::Expr, ::CSEState) = x
cse!(x::LiteralExpr, ::CSEState) = x

cse!(x::CodegenPrimitive, state::CSEState) = throw(MethodError(cse!, (x, state)))

cse!(x::AbstractRange, ::CSEState) = x
function cse!(x::AbstractArray, state::CSEState)
    res = map(Base.Fix2(cse!, state), x)
    return res
end

function cse!(x::AbstractSparseArray, state::CSEState)
    new_x = copy(x)
    for (i, j, v) in zip(findnz(x)...)
        new_x[i, j] = cse!(v, state)
    end
    return new_x
end

function cse!(x::Tuple, state::CSEState)
    res = map(Base.Fix2(cse!, state), x)
    return res
end

function cse!(x::MakeArray, state::CSEState)
    return MakeArray(cse!(x.elems, state), x.similarto, x.output_eltype)
end

function cse!(x::SetArray, state::CSEState)
    return SetArray(x.inbounds, x.arr, cse!(x.elems, state), x.return_arr)
end

function cse!(x::MakeSparseArray, state::CSEState)
    m, n = size(x.array)
    i, j, v = findnz(x.array)
    return MakeSparseArray(sparse(i, j, cse!(v, state), m, n))
end

function cse!(x::Assignment, state::CSEState)
    return Assignment(x.lhs, cse!(x.rhs, state))
end

function cse!(x::DestructuredArgs, state::CSEState)
    return DestructuredArgs(x.elems, x.inds, cse!(x.name, state), x.inbounds, x.create_bindings)
end

function cse!(x::Let, state::CSEState)
    state = new_scope(state)
    # `Let` introduces a new scope. For each assignment `p` in `x.pairs`, we CSE it
    # and then append it to the new assignments from CSE. This is because the assignments
    # are imperative, so the CSE assignments for a given `p` can include previous `p`,
    # preventing us from simply wrapping the `Let` in another `Let`.
    for p in x.pairs
        newp = cse!(p, state)
        push!(state.sorted_exprs, newp)
    end
    newbody = cse!(x.body, state)
    return Let(state.sorted_exprs, newbody, x.let_block)
end

function cse!(x::Func, state::CSEState)
    state = new_scope(state)
    return Func(x.args, x.kwargs, apply_cse(cse!(x.body, state), state), x.pre)
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

end
