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

@inline take_n(ll::LL, n) = isempty(ll) || n == 0 ? empty(ll) : @views ll.v[ll.i:n+ll.i-1] # @views handles Tuple
@inline take_n(ll, n) = @views ll[1:n]

drop_n(ll, n) = n === 0 ? ll : drop_n(cdr(ll), n-1)

@inline drop_n(ll::Term, n) = drop_n(arguments(ll), n-1)
@inline drop_n(ll::AbstractArray, n) = drop_n(LL(ll, 1), n)
@inline drop_n(ll::LL, n) = LL(ll.v, ll.i+n)

@inline assoc(d::Dict, k, v) = merge(d, Dict(k=>v))
@inline assoc(f, d::Dict, k, v) = merge(f, d, Dict(k=>v))

@inline assoc(d::NamedTuple, k, v) = Base.setindex(d, v, k)
@inline assoc(f, d::NamedTuple, k, v) = Base.setindex(d, v, k)
