struct LL{V}
    v::V
    i::Int
end

islist(::Any) = false
islist(l::Union{LL, Term, AbstractArray, Tuple}) = true

Base.empty(l::LL) = empty(l.v)
Base.isempty(l::LL) = l.i > length(l.v)

Base.length(l::LL) = length(l.v)-l.i+1
@inline car(l::LL) = l.v[l.i]
@inline cdr(l::LL) = isempty(l) ? empty(l) : LL(l.v, l.i+1)

Base.length(t::Term) = length(arguments(t)) + 1 # PIRACY
Base.isempty(t::Term) = false
@inline car(t::Term) = operation(t)
@inline cdr(t::Term) = arguments(t)

@inline car(v) = first(v)
@inline cdr(v) = isempty(v) ? empty(l) : LL(v, 2)

@inline take_n(ll::LL, n) = isempty(ll) || n == 0 ? empty(ll) : @view ll.v[ll.i:min(end, n+ll.i-1)]
@inline take_n(ll, n) = @view ll[1:min(end, n)]

@inline drop_n(ll::Term, n) = drop_n(arguments(ll), n)
@inline drop_n(ll::Array, n) = drop_n(LL(ll, 1), n)
@inline drop_n(ll::LL, n) = LL(ll.v, max(1, ll.i-n))

@inline assoc(d::Dict, k, v) = merge(d, Dict(k=>v))
@inline assoc(f, d::Dict, k, v) = merge(f, d, Dict(k=>v))
