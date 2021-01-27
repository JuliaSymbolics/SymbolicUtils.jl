# Take a struct definition and make it be able to match in `@rule`
macro matchable(expr)
    @assert expr.head == :struct
    name = expr.args[2]
    if name isa Expr && name.head === :curly
        name = name.args[1]
    end
    fields = expr.args[3].args  # Todo: get names
    quote
        $expr
        SymbolicUtils.istree(::$name) = true
        SymbolicUtils.operation(::$name) = $name
        SymbolicUtils.arguments(::$name) = ($(fields...),)
    end |> esc
end

toexpr(s::Sym, st) = nameof(s)

@matchable struct Assignment
    lhs
    rhs
end

const (←) = Assignment

Base.convert(::Type{Assignment}, p::Pair) = Assignment(pair[1], pair[2])

toexpr(a::Assignment, st) = :($(toexpr(a.lhs, st)) = $(toexpr(b.lhs, st)))

struct NameState
    tosym::Dict
    sym_count::Dict
    destructed_args::Dict
end
NameState() = NameState(Dict{Any, Sym}(), Dict{Sym, Int}(), IdDict())

struct LazyState
    ref::Ref{Any}
end
LazyState() = LazyState(Ref{Any}(nothing))

function Base.get(st::LazyState)
    s = getfield(st, :ref)[]
    s === nothing ? getfield(st, :ref)[] = NameState() : s
end

@inline Base.getproperty(st::LazyState, f::Symbol) = getproperty(get(st), f)

function toexpr(O, st)
    !istree(O) && return O
    op = operation(O)
    args = arguments(O)
    if op isa Differential
        ex = toexpr(args[1], st)
        wrt = toexpr(op.x, st)
        return :(_derivative($ex, $wrt))
    elseif op isa Sym
        isempty(args) && return nameof(op)
        return Expr(:call, toexpr(op, st), toexpr(args, st)...)
    elseif op === (^) && length(args) == 2 && args[2] isa Number && args[2] < 0
        ex = toexpr(args[1], st)
        if args[2] == -1
            return toexpr(Term{Any}(inv, ex), st)
        else
            return toexpr(Term{Any}(^, [Term{Any}(inv, ex), -args[2]]), st)
        end
    elseif op === (cond)
        :($(toexpr(args[1], st)) ? $(toexpr(args[2], st)) : $(toexpr(args[3], st)))
    elseif op isa Sym # We can just use it as a variable
        get!(st.tosym, O) do
            c = get(st.sym_count, op, 0)
            sym = c != 0 ? Symbol(op, :__, c) : op
            st.tosym[O] = sym
            st.sym_count[sym] = c + 1
        end
    end
    return Expr(:call, op, toexpr(args, st)...)
end

@matchable struct Let
    pairs::Vector{Assignment} # an iterator of pairs, ordered
    body
end

function toexpr(l::Let, st)
    assignments = Expr(:block,
                       [:($k = $v) for (k, v) in l.pairs]...)

    Expr(:let, assignments, toexpr(l.expr, st))
end

### Experimental
@matchable struct BasicBlock
    pairs::Vector{Assignment} # Iterator of ordered pairs
    # TODO: check uniqueness of LHS on construction
end

function toexpr(l::BasicBlock, st)
    stmts = [:($(toexpr(k, st)) = $(toexpr(v, st))) for (k, v) in l.pairs]
    Expr(:block, stmts)
end

# Call elements of vector arguments by their name.
@matchable struct DeStructArgs
    elems
end

function toexpr(args::DeStructArgs, st)
    st.destructed_args[args] = gensym("arg")
end

@matchable struct Func
    args
    kwargs
    body
end

function toexpr(f::Func, st)
    quote
        function ($(map(x->toexpr(x, st), f.args)...),; $(map(x->toexpr(x, st), f.kwargs)...))
            $(toexpr(f.body, st))
        end
    end
end


@matchable struct SetArray
    inbounds::Bool
    arr::Sym
    elems  # Either iterator of Pairs or just an iterator
end

@matchable struct AtIndex
    i::Int
    elem
end

function toexpr(a::AtIndex, st)
    toexpr(a.elem, st)
end

function toexpr(s::SetArray, st)
    ex = quote
        $([:($(toexpr(s.arr, st))[$(ex isa AtIndex ? ex.i : i)] = $(toexpr(ex, st)))
           for (i, ex) in enumerate(s.elems)]...)
        nothing
    end
    s.inbounds ? :(@inbounds begin $ex end) : ex
end

@matchable struct MakeArray{A<:AbstractArray} # Could be StaticArray
    elems::A
end

function toexpr(a::MakeArray, st)
    :([$(toexpr.(a.elems, (st,))...)])
end

using SparseArrays

## We use a separate type for Sparse Arrays to sidestep the need for
## iszero to be defined on the expression type
@matchable struct MakeSparseArray
    sparsity::SparseMatrixCSC
    V
end

function MakeSparseArray(I, J, V)
end

function toexpr(a::MakeArray, st)
    sp = a.sparsity
    :(SparseMatrixCSC(sp.m, sp.n, sp.colptr, sp.rowval, [$(toexpr.(a.elems, (st,))...)]))
end

@matchable struct MakeTuple
    elems
end

function toexpr(a::MakeTuple, st)
    :(($(toexpr.(a.elems, (st,))...),))
end
