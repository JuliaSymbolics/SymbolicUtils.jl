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
   returns true, `rw2` if it returns false
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
using TermInterface

import SymbolicUtils: iscall, operation, arguments, sorted_arguments, metadata, node_count, _promote_symtype
export Empty, IfElse, If, Chain, RestartedChain, Fixpoint, Postwalk, Prewalk, PassThrough

# Cache of printed rules to speed up @timer
const repr_cache = IdDict()
cached_repr(x) = Base.get!(()->repr(x), repr_cache, x)

"""
    Empty()

A rewriter that always returns `nothing`, indicating no rewrite occurred.

This is useful as a placeholder or for conditional rewriting patterns.

# Examples
```julia
julia> Empty()(x)
nothing
```
"""
struct Empty end

(rw::Empty)(x) = nothing

instrument(x, f) = f(x)
instrument(x::Empty, f) = x

"""
    IfElse(cond, yes, no)

A conditional rewriter that applies `yes` if `cond(x)` is true, otherwise applies `no`.

# Arguments
- `cond`: A function that returns true or false for the input
- `yes`: The rewriter to apply if the condition is true
- `no`: The rewriter to apply if the condition is false

# Examples
```julia
julia> r = IfElse(x -> x > 0, x -> -x, x -> x)
julia> r(5)  # Returns -5
julia> r(-3) # Returns -3
```

See also: [`If`](@ref)
"""
struct IfElse{F, A, B}
    cond::F
    yes::A
    no::B
end

instrument(x::IfElse, f) = IfElse(x.cond, instrument(x.yes, f), instrument(x.no, f))

function (rw::IfElse)(x)
    rw.cond(x) ?  rw.yes(x) : rw.no(x)
end

"""
    If(cond, yes)

A conditional rewriter that applies `yes` if `cond(x)` is true, otherwise returns the input unchanged.

This is equivalent to `IfElse(cond, yes, Empty())`.

# Arguments
- `cond`: A function that returns true or false for the input
- `yes`: The rewriter to apply if the condition is true

# Examples
```julia
julia> r = If(x -> x > 0, x -> -x)
julia> r(5)  # Returns -5
julia> r(-3) # Returns -3 (unchanged)
```
"""
If(f, x) = IfElse(f, x, Empty())

"""
    Chain(rws; stop_on_match=false)

Apply a sequence of rewriters to an expression, chaining the results.

Each rewriter in the chain receives the result of the previous rewriter.
If a rewriter returns `nothing`, the input is passed unchanged to the next rewriter.

# Arguments
- `rws`: A collection of rewriters to apply in sequence
- `stop_on_match`: If true, stop at the first rewriter that produces a change

# Examples
```julia
julia> r1 = @rule sin(~x)^2 + cos(~x)^2 => 1
julia> r2 = @rule sin(2*(~x)) => 2*sin(~x)*cos(~x)
julia> chain = Chain([r1, r2])
julia> chain(sin(x)^2 + cos(x)^2)  # Returns 1
```
"""
struct Chain
    rws
    stop_on_match::Bool
end
Chain(rws) = Chain(rws, false)

function (rw::Chain)(x)
    for f in rw.rws
        y = @timer cached_repr(f) f(x)
        if rw.stop_on_match && !isnothing(y) && !isequal(y, x)
            return y
        end

        if y !== nothing
            x = y
        end
    end
    return x

end
instrument(c::Chain, f) = Chain(map(x->instrument(x,f), c.rws))

"""
    RestartedChain(rws)

Apply rewriters in sequence, restarting the chain when any rewriter produces a change.

When any rewriter in the chain produces a non-nothing result, the entire chain
is restarted with that result as the new input.

# Arguments
- `rws`: A collection of rewriters to apply

# Examples
```julia
julia> r1 = @rule ~x + ~x => 2 * ~x
julia> r2 = @rule 2 * ~x => ~x * 2
julia> chain = RestartedChain([r1, r2])
julia> chain(x + x)  # Applies r1, then restarts and applies r2
```
"""
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


"""
    Fixpoint(rw)

Apply a rewriter repeatedly until a fixed point is reached.

The rewriter is applied repeatedly until the output equals the input
(either by identity or by `isequal`), indicating a fixed point has been reached.

# Arguments
- `rw`: The rewriter to apply repeatedly

# Examples
```julia
julia> r = @rule ~x + ~x => 2 * ~x
julia> fp = Fixpoint(r)
julia> fp(x + x + x + x)  # Keeps applying until no more changes
```

See also: [`FixpointNoCycle`](@ref)
"""
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
    while x !== y && hash(x) ∉ rw.hist
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
    maketerm::F
end

function instrument(x::Walk{ord, C,F,threaded}, f) where {ord,C,F,threaded}
    irw = instrument(x.rw, f)
    Walk{ord, typeof(irw), typeof(x.maketerm), threaded}(irw,
                                                            x.thread_cutoff,
                                                            x.maketerm)
end

using .Threads


"""
    Postwalk(rw; threaded=false, thread_cutoff=100, maketerm=maketerm)

Apply a rewriter to a symbolic expression tree in post-order (bottom-up).

Post-order traversal visits child nodes before their parents, allowing for
simplification of subexpressions before the containing expression.

# Arguments
- `rw`: The rewriter to apply at each node
- `threaded`: If true, use multi-threading for large expressions
- `thread_cutoff`: Minimum node count to trigger threading
- `maketerm`: Function to construct terms (defaults to `maketerm`)

# Examples
```julia
julia> r = @rule ~x + ~x => 2 * ~x
julia> pw = Postwalk(r)
julia> pw((x + x) * (y + y))  # Simplifies both additions
2x * 2y
```

See also: [`Prewalk`](@ref)
"""
function Postwalk(rw; threaded::Bool=false, thread_cutoff=100, maketerm=maketerm)
    Walk{:post, typeof(rw), typeof(maketerm), threaded}(rw, thread_cutoff, maketerm)
end

"""
    Prewalk(rw; threaded=false, thread_cutoff=100, maketerm=maketerm)

Apply a rewriter to a symbolic expression tree in pre-order (top-down).

Pre-order traversal visits parent nodes before their children, allowing for
transformation of the overall structure before processing subexpressions.

# Arguments
- `rw`: The rewriter to apply at each node
- `threaded`: If true, use multi-threading for large expressions
- `thread_cutoff`: Minimum node count to trigger threading
- `maketerm`: Function to construct terms (defaults to `maketerm`)

# Examples
```julia
julia> r = @rule sin(~x) => cos(~x)
julia> pw = Prewalk(r)
julia> pw(sin(sin(x)))  # Transforms outer sin first
cos(cos(x))
```

See also: [`Postwalk`](@ref)
"""
function Prewalk(rw; threaded::Bool=false, thread_cutoff=100, maketerm=maketerm)
    Walk{:pre, typeof(rw), typeof(maketerm), threaded}(rw, thread_cutoff, maketerm)
end

"""
    PassThrough(rw)

A rewriter that returns the input unchanged if the wrapped rewriter returns `nothing`.

This is useful for making rewriters that preserve the input when no rule applies.

# Arguments
- `rw`: The rewriter to wrap

# Examples
```julia
julia> r = @rule sin(~x) => cos(~x)
julia> pt = PassThrough(r)
julia> pt(sin(x))  # Returns cos(x)
julia> pt(tan(x))  # Returns tan(x) unchanged
```
"""
struct PassThrough{C}
    rw::C
end
instrument(x::PassThrough, f) = PassThrough(instrument(x.rw, f))

(p::PassThrough)(x) = (y=p.rw(x); y === nothing ? x : y)

passthrough(x, default) = x === nothing ? default : x
function (p::Walk{ord, C, F, false})(x) where {ord, C, F}
    @assert ord === :pre || ord === :post
    if iscall(x)
        if ord === :pre
            x = p.rw(x)
        end

        if iscall(x)
            x = p.maketerm(typeof(x), operation(x), map(PassThrough(p),
                            arguments(x)), metadata(x))
        end

        return ord === :post ? p.rw(x) : x
    else
        return p.rw(x)
    end
end

function (p::Walk{ord, C, F, true})(x) where {ord, C, F}
    @assert ord === :pre || ord === :post
    if iscall(x)
        if ord === :pre
            x = p.rw(x)
        end
        if iscall(x)
            _args = map(arguments(x)) do arg
                if node_count(arg) > p.thread_cutoff
                    Threads.@spawn p(arg)
                else
                    p(arg)
                end
            end
            args = map((t,a) -> passthrough(t isa Task ? fetch(t) : t, a), _args, arguments(x))
            t = p.maketerm(typeof(x), operation(x), args, metadata(x))
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


