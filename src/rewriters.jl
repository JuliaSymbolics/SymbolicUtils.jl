"""
A rewriter is any function which takes an expression and returns an expression
or `nothing`. If `nothing` is returned that means there was no changes applicable
to the input expression.

The `SymbolicUtils.Rewriters` module contains some types which create and transform
rewriters.

- `Empty()` is a rewriter which always returns `nothing`
- `Chain(itr)` chain an iterator of rewriters into a single rewriter which applies
   each chained rewriter in the given order.
   If a rewriter returns `nothing` this is treated as a no-change.
- `RestartedChain(itr)` like `Chain(itr)` but restarts on the first successful application
   of one of the chained rewriters.
- `Prewalk(rw; threaded=false, thread_cutoff=100)` returns a rewriter which does a pre-order
   traversal of a given expression and applies the rewriter `rw`. `threaded=true` will
   use multi threading for traversal. `thread_cutoff` is the minimum number of nodes
   in a subtree which should be walked in a threaded spawn.
- `Postwalk(rw; threaded=false, thread_cutoff=100)` similarly does post-order traversal.
- `IfElse(cond, rw1, rw2)` runs the `cond` function on the input, applies `rw1` if cond
   returns true, `rw2` if it retuns false
- `If(cond, rw)` is the same as `IfElse(cond, rw, Empty())`
- `PassThrough(rw)` returns a rewriter which if `rw(x)` returns `nothing` will instead
   return `x` otherwise will return `rw(x)`.
"""
module Rewriters
using SymbolicUtils: @timer, is_operation, istree, symtype, Term, operation, arguments,
                     node_count

export Empty, IfElse, If, Chain, RestartedChain, Fixpoint, Postwalk, Prewalk, PassThrough

struct Empty end

(ctx::Empty)(x) = nothing

struct IfElse{F, A, B}
    cond::F
    yes::A
    no::B
end

function (ctx::IfElse)(x)
    ctx.cond(x) ?  ctx.yes(x) : ctx.no(x)
end

If(f, x) = IfElse(f, x, Empty())

struct Chain{Cs}
    ctxs::Cs
end

function (ctx::Chain)(x)
    for f in ctx.ctxs
        y = @timer Base.@get!(rule_repr, f, repr(f)) f(x)
        if y !== nothing
            x = y
        end
    end
    return x
end

struct RestartedChain{Cs}
    ctxs::Cs
end

function (ctx::RestartedChain)(x)
    for f in ctx.ctxs
        y = @timer Base.@get!(rule_repr, f, repr(f)) f(x)
        if y !== nothing
            return Chain(ctx.ctxs)(y)
        end
    end
    return x
end

struct Fixpoint{C}
    ctx::C
end

const rule_repr = IdDict()

function (ctx::Fixpoint)(x)
    f = ctx.ctx
    y = @timer Base.@get!(rule_repr, f, repr(f)) f(x)
    while x !== y && !isequal(x, y)
        isnothing(y) && return x
        x = y
        y = @timer Base.@get!(rule_repr, f, repr(f)) f(x)
    end
    return x
end

struct Walk{ord, C, threaded}
    ctx::C
    thread_cutoff::Int
end

using .Threads

function Postwalk(ctx; threaded::Bool=false, thread_cutoff=100)
    Walk{:post, typeof(ctx), threaded}(ctx, thread_cutoff)
end

function Prewalk(ctx; threaded::Bool=false, thread_cutoff=100)
    Walk{:pre, typeof(ctx), threaded}(ctx, thread_cutoff)
end

struct PassThrough{C}
    ctx::C
end
(p::PassThrough)(x) = (y=p.ctx(x); isnothing(y) ? x : y)

passthrough(x, default) = isnothing(x) ? default : x
function (p::Walk{ord, C, false})(x) where {ord, C}
    @assert ord === :pre || ord === :post
    if istree(x)
        if ord === :pre
            x = p.ctx(x)
        end
        if istree(x)
            x = Term{symtype(x)}(operation(x),
                                 map(t->PassThrough(p)(t),
                                     arguments(x)))
        end
        return ord === :post ? p.ctx(x) : x
    else
        return p.ctx(x)
    end
end

function (p::Walk{ord, C, true})(x) where {ord, C}
    @assert ord === :pre || ord === :post
    if istree(x)
        if ord === :pre
            x = p.ctx(x)
        end
        if istree(x)
            _args = map(arguments(x)) do arg
                if node_count(arg) > p.thread_cutoff
                    Threads.@spawn p(arg)
                else
                    p(arg)
                end
            end
            args = map((t,a) -> passthrough(t isa Task ? fetch(t) : t, a), _args, arguments(x))
            t = Term{symtype(x)}(operation(x), args)
        end
        return ord === :post ? p.ctx(t) : t
    else
        return p.ctx(x)
    end
end

end # end module

