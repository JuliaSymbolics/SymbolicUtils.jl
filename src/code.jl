# Take a struct definition and make it be able to match in `@rule`
macro matchable(expr)
    @assert expr.head == :struct
    name = expr.args[2]
    fields = expr.args[3].args  # Todo: get names
    quote
        $expr
        SymbolicUtils.istree(::$name) = true
        SymbolicUtils.operation(::$name) = $name
        SymbolicUtils.arguments(::$name) = ($(fields...),)
    end |> esc
end

toexpr(s::Sym) = nameof(s)

@matchable struct Assignment
    lhs
    rhs
end

const (←) = Assignment

Base.convert(::Type{Assignment}, p::Pair) = Assignment(pair[1], pair[2])

toexpr(a::Assignment) = :($(toexpr(a.lhs)) = $(toexpr(b.lhs)))

function toexpr(O)
    !istree(O) && return O
    op = operation(O)
    args = arguments(O)
    if op isa Differential
        ex = toexpr(args[1])
        wrt = toexpr(op.x)
        return :(_derivative($ex, $wrt))
    elseif op isa Sym
        isempty(args) && return nameof(op)
        return Expr(:call, toexpr(op), toexpr(args)...)
    elseif op === (^) && length(args) == 2 && args[2] isa Number && args[2] < 0
        ex = toexpr(args[1])
        if args[2] == -1
            return toexpr(Term{Any}(inv, ex))
        else
            return toexpr(Term{Any}(^, [Term{Any}(inv, ex), -args[2]]))
        end
    elseif op === (cond)
        :($(toexpr(args[1])) ? $(toexpr(args[2])) : $(toexpr(args[3])))
    end
    return Expr(:call, op, toexpr(args)...)
end

@matchable struct Let
    pairs::Vector{Assignment} # an iterator of pairs, ordered
    body
end

function toexpr(l::Let)
    assignments = Expr(:block,
                       [:($k = $v) for (k, v) in l.pairs]...)

    Expr(:let, assignments, toexpr(l.expr))
end

### Experimental
@matchable struct BasicBlock
    pairs::Vector{Assignment} # Iterator of ordered pairs
    # TODO: check uniqueness of LHS on construction
end

function toexpr(l::BasicBlock)
    stmts = [:($k = $v) for (k, v) in l.pairs]
    Expr(:block, stmts)
end

# Requirements
#
#                   Scalar inputs     Vector inputs
#
# Scalar output
# Vector outputs
# multiple outputs
#
#
# Array types: Dense, Sparse, Static
#
#
@matchable struct Func
    args
    kwargs
    body
end

function toexpr(f::Func)
    quote
        function ($(map(toexpr, f.args)...),; $(map(toexpr, f.kwargs)...))
            $(toexpr(f.body))
        end
    end
end


@matchable struct SetArray
    arr::Sym
    elems  # Either iterator of Pairs or just an iterator
end

@matchable struct AtIndex
    i::Int
    elem
end

function toexpr(a::AtIndex)
    toexpr(a.elem)
end

function toexpr(s::SetArray)
    quote
        $([:($(toexpr(s.arr))[$(ex isa AtIndex ? ex.i : i)]) = $(toexpr(ex))
           for (i, ex) in enumerate(s.elems)]...)
        nothing
    end
end

@matchable struct MakeArray{A<:AbstractArray} # Could be StaticArray
    elems::A
end

function toexpr(a::MakeArray)
    :([$(toexpr.(a.elems)...)])
end

## We use a separate type for Sparse Arrays to sidestep the need for
## iszero to be defined on the expression type
@matchable struct MakeSparseArray
    I
    J
    V
end

@matchable struct MakeTuple
    elems
end

function toexpr(a::MakeTuple)
    :(($(toexpr.(a.elems)...),))
end
