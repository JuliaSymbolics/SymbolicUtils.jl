"""
A rewriter is any function which takes an expression and returns an expression
or `nothing`. If `nothing` is returned that means there was no changes applicable
to the input expression.

The `Rewriters` module contains some types which create and transform
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
   traversal of a given expression and applies the rewriter `rw`. Note that if
   `rw` returns `nothing` when a match is not found, then `Prewalk(rw)` will
   also return nothing unless a match is found at every level of the walk.
   `threaded=true` will use multi threading for traversal. `thread_cutoff` is
   the minimum number of nodes in a subtree which should be walked in a
   threaded spawn.
- `Postwalk(rw; threaded=false, thread_cutoff=100)` similarly does post-order traversal.
- `Fixpoint(rw)` returns a rewriter which applies `rw` repeatedly until there are no changes to be made.
- `FixpointNoCycle` behaves like [`Fixpoint`](@ref) but instead it applies `rw` repeatedly only while it is returning new results.
- `PassThrough(rw)` returns a rewriter which if `rw(x)` returns `nothing` will instead
   return `x` otherwise will return `rw(x)`.

"""
module Rewriters
using SymbolicUtils: @timer

import SymbolicUtils: similarterm, istree, operation, arguments, unsorted_arguments, node_count
export Empty, IfElse, If, Chain, RestartedChain, Fixpoint, Postwalk, Prewalk, PassThrough

# Cache of printed rules to speed up @timer
const repr_cache = IdDict()
cached_repr(x) = Base.get!(()->repr(x), repr_cache, x)

struct Empty end

(rw::Empty)(x) = nothing

instrument(x, f) = f(x)
instrument(x::Empty, f) = x

struct IfElse{F, A, B}
    cond::F
    yes::A
    no::B
end

instrument(x::IfElse, f) = IfElse(x.cond, instrument(x.yes, f), instrument(x.no, f))

function (rw::IfElse)(x)
    rw.cond(x) ?  rw.yes(x) : rw.no(x)
end

If(f, x) = IfElse(f, x, Empty())

struct Chain
    rws
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

instrument(c::Chain, f) = Chain(map(x->instrument(x,f), c.rws))

struct RestartedChain{Cs}
    rws::Cs
end

instrument(c::RestartedChain, f) = RestartedChain(map(x->instrument(x,f), c.rws))

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

instrument(x::Fixpoint, f) = Fixpoint(instrument(x.rw, f))

function (rw::Fixpoint)(x)
    f = rw.rw
    y = @timer cached_repr(f) f(x)
    while x !== y && !isequal(x, y)
        y === nothing && return x
        x = y
        y = @timer cached_repr(f) f(x)
    end
    return x
end

"""
    FixpointNoCycle(rw)

`FixpointNoCycle` behaves like [`Fixpoint`](@ref),
but returns a rewriter which applies `rw` repeatedly until 
it produces a result that was already produced before, for example, 
if the repeated application of `rw` produces results `a, b, c, d, b` in order, 
`FixpointNoCycle` stops because `b` has been already produced. 
"""
struct FixpointNoCycle{C}
    rw::C
    hist::Vector{UInt64} # vector of hashes for history
end

instrument(x::FixpointNoCycle, f) = Fixpoint(instrument(x.rw, f))

function (rw::FixpointNoCycle)(x)
    f = rw.rw
    push!(rw.hist, hash(x))
    y = @timer cached_repr(f) f(x)
    while x !== y && hash(x) ∉ hist
        if y === nothing 
            empty!(rw.hist)
            return x
        end
        push!(rw.hist, y)
        x = y
        y = @timer cached_repr(f) f(x)
    end
    empty!(rw.hist)
    return x
end

struct Walk{ord, C, F, threaded}
    rw::C
    thread_cutoff::Int
    similarterm::F
end

function instrument(x::Walk{ord, C,F,threaded}, f) where {ord,C,F,threaded}
    irw = instrument(x.rw, f)
    Walk{ord, typeof(irw), typeof(x.similarterm), threaded}(irw,
                                                            x.thread_cutoff,
                                                            x.similarterm)
end

using .Threads

function Postwalk(rw; threaded::Bool=false, thread_cutoff=100, similarterm=similarterm)
    Walk{:post, typeof(rw), typeof(similarterm), threaded}(rw, thread_cutoff, similarterm)
end

function Prewalk(rw; threaded::Bool=false, thread_cutoff=100, similarterm=similarterm)
    Walk{:pre, typeof(rw), typeof(similarterm), threaded}(rw, thread_cutoff, similarterm)
end

struct PassThrough{C}
    rw::C
end
instrument(x::PassThrough, f) = PassThrough(instrument(x.rw, f))

(p::PassThrough)(x) = (y=p.rw(x); y === nothing ? x : y)

passthrough(x, default) = x === nothing ? default : x
function (p::Walk{ord, C, F, false})(x) where {ord, C, F}
    @assert ord === :pre || ord === :post
    if istree(x)
        if ord === :pre
            x = p.rw(x)
        end
        if istree(x)
            x = p.similarterm(x, operation(x), map(PassThrough(p), unsorted_arguments(x)))
        end
        return ord === :post ? p.rw(x) : x
    else
        return p.rw(x)
    end
end

function (p::Walk{ord, C, F, true})(x) where {ord, C, F}
    @assert ord === :pre || ord === :post
    if istree(x)
        if ord === :pre
            x = p.rw(x)
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
            t = p.similarterm(x, operation(x), args)
        end
        return ord === :post ? p.rw(t) : t
    else
        return p.rw(x)
    end
end

function instrument_io(x)
    function io_instrumenter(r)
        function (args...)
            println("Rule: ", r)
            println("Input: ", args)
            res = r(args...)
            println("Output: ", res)
            res
        end
    end

    instrument(x, io_instrumenter)
end

end # end module


