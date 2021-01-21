const TIMER_OUTPUTS = true
const being_timed = Ref{Bool}(false)

if TIMER_OUTPUTS
    using TimerOutputs

    macro timer(name, expr)
        :(if being_timed[]
              @timeit $(esc(name)) $(esc(expr))
          else
              $(esc(expr))
          end)
    end

    macro iftimer(expr)
        esc(expr)
    end

else
    macro timer(name, expr)
        esc(expr)
    end

    macro iftimer(expr)
    end
end

using Base: ImmutableDict

# Linked List interface
@inline assoc(d::ImmutableDict, k, v) = ImmutableDict(d, k=>v)

struct LL{V}
    v::V
    i::Int
end

islist(x) = istree(x) || !isempty(x)

Base.empty(l::LL) = empty(l.v)
Base.isempty(l::LL) = l.i > length(l.v)

Base.length(l::LL) = length(l.v)-l.i+1
@inline car(l::LL) = l.v[l.i]
@inline cdr(l::LL) = isempty(l) ? empty(l) : LL(l.v, l.i+1)

Base.length(t::Term) = length(arguments(t)) + 1 # PIRACY
Base.isempty(t::Term) = false
@inline car(t::Term) = operation(t)
@inline cdr(t::Term) = arguments(t)

@inline car(v) = istree(v) ? operation(v) : first(v)
@inline function cdr(v)
    if istree(v)
        arguments(v)
    else
        islist(v) ? LL(v, 2) : error("asked cdr of empty")
    end
end

@inline take_n(ll::LL, n) = isempty(ll) || n == 0 ? empty(ll) : @views ll.v[ll.i:n+ll.i-1] # @views handles Tuple
@inline take_n(ll, n) = @views ll[1:n]

@inline function drop_n(ll, n)
    if n === 0
        return ll
    else
        istree(ll) ? drop_n(arguments(ll), n-1) : drop_n(cdr(ll), n-1)
    end
end
@inline drop_n(ll::Union{Tuple, AbstractArray}, n) = drop_n(LL(ll, 1), n)
@inline drop_n(ll::LL, n) = LL(ll.v, ll.i+n)
