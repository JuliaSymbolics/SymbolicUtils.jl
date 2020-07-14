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
- `RestartedChain(itr)` like `Chain(itr)` but restarts from the first rewriter once on the
   first successful application of one of the chained rewriters.
- `IfElse(cond, rw1, rw2)` runs the `cond` function on the input, applies `rw1` if cond
   returns true, `rw2` if it retuns false
- `If(cond, rw)` is the same as `IfElse(cond, rw, Empty())`
- `Prewalk(rw; threaded=false, thread_cutoff=100)` returns a rewriter which does a pre-order
   traversal of a given expression and applies the rewriter `rw`. `threaded=true` will
   use multi threading for traversal. `thread_cutoff` is the minimum number of nodes
   in a subtree which should be walked in a threaded spawn.
- `Postwalk(rw; threaded=false, thread_cutoff=100)` similarly does post-order traversal.
- `Fixpoint(rw)` returns a rewriter which applies `rw` repeatedly until there are no changes to be made.
- `PassThrough(rw)` returns a rewriter which if `rw(x)` returns `nothing` will instead
   return `x` otherwise will return `rw(x)`.

"""
module Rewriters
using SymbolicUtils: @timer, is_operation, istree, symtype, Term, operation, arguments,
                     num_descendants

export Empty, IfElse, If, Chain, RestartedChain, Fixpoint, Postwalk, Prewalk, PassThrough

# Cache of printed rules to speed up @timer
const repr_cache = IdDict()
cached_repr(x) = Base.get!(()->repr(x), repr_cache, x)

struct Empty end

(rw::Empty)(x) = nothing

struct IfElse{F, A, B}
    cond::F
    yes::A
    no::B
end

function (rw::IfElse)(x)
    rw.cond(x) ?  rw.yes(x) : rw.no(x)
end

If(f, x) = IfElse(f, x, Empty())

struct Chain{Cs}
    rws::Cs
end

function (rw::Chain)(x)
    for f in rw.rws
        y = @timer cached_repr(f) f(x)
        if y !== nothing
            x = y
        end
    end
    return x
end

@generated function (rw::Chain{<:NTuple{N,Any}})(x) where N
    quote
        Base.@nexprs $N i->begin
            let f = rw.rws[i]
                y = @timer cached_repr(f) f(x)
                if y !== nothing
                    x = y
                end
            end
        end
        return x
    end
end

struct RestartedChain{Cs}
    rws::Cs
end

function (rw::RestartedChain)(x)
    for f in rw.rws
        y = @timer cached_repr(f) f(x)
        if y !== nothing
            return Chain(rw.rws)(y)
        end
    end
    return x
end

@generated function (rw::RestartedChain{<:NTuple{N,Any}})(x) where N
    quote
        Base.@nexprs $N i->begin
            let f = rw.rws[i]
                y = @timer cached_repr(repr(f)) f(x)
                if y !== nothing
                    return Chain(rw.rws)(y)
                end
            end
        end
        return x
    end
end
struct Fixpoint{C}
    rw::C
end

function (rw::Fixpoint)(x)
    f = rw.rw
    y = @timer cached_repr(f) f(x)
    while x !== y && !isequal(x, y)
        isnothing(y) && return x
        x = y
        y = @timer cached_repr(f) f(x)
    end
    return x
end

struct Walk{ord, C, threaded}
    rw::C
    thread_cutoff::Int
end

using .Threads

function Postwalk(rw; threaded::Bool=false, thread_cutoff=100)
    Walk{:post, typeof(rw), threaded}(rw, thread_cutoff)
end

function Prewalk(rw; threaded::Bool=false, thread_cutoff=100)
    Walk{:pre, typeof(rw), threaded}(rw, thread_cutoff)
end

struct PassThrough{C}
    rw::C
end
(p::PassThrough)(x) = (y=p.rw(x); isnothing(y) ? x : y)

passthrough(x, default) = isnothing(x) ? default : x
function (p::Walk{ord, C, false})(x) where {ord, C}
    @assert ord === :pre || ord === :post
    if istree(x)
        if ord === :pre
            x = p.rw(x)
        end
        if istree(x)
            x = Term{symtype(x)}(operation(x),
                                 map(t->PassThrough(p)(t),
                                     arguments(x)))
        end
        return ord === :post ? p.rw(x) : x
    else
        return p.rw(x)
    end
end

function (p::Walk{ord, C, true})(x) where {ord, C}
    @assert ord === :pre || ord === :post
    if istree(x)
        if ord === :pre
            x = p.rw(x)
        end
        if istree(x)
            _args = map(arguments(x)) do arg
                if num_descendants(arg) > p.thread_cutoff
                    Threads.@spawn p(arg)
                else
                    p(arg)
                end
            end
            args = map((t,a) -> passthrough(t isa Task ? fetch(t) : t, a), _args, arguments(x))
            t = Term{symtype(x)}(operation(x), args)
        end
        return ord === :post ? p.rw(t) : t
    else
        return p.rw(x)
    end
end

end # end module

