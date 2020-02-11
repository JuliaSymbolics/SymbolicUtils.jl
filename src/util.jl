struct LL{V}
    v::V
    i::Int
end

islist(::Any) = false
islist(l::Union{LL, Term, AbstractArray, Tuple}) = true

Base.isempty(l::LL) = l.i > length(l.v)

Base.length(l::LL) = length(l.v)-l.i+1
@inline car(l::LL) = l.v[l.i]
@inline cdr(l::LL) = isempty(l) ? () : LL(l.v, l.i+1)

Base.length(t::Term) = length(arguments(t)) + 1 # PIRACY
Base.isempty(t::Term) = false
@inline car(t::Term) = operation(t)
@inline cdr(t::Term) = arguments(t)

@inline car(v) = first(v)
@inline function cdr(v)
    if isempty(v)
        return ()
    else
        # return a linked list starting at 2
        return LL(v, 2)
    end
end

struct Cons
    car
    cdr
end
islist(c::Cons) = true

@inline cons(car,cdr) = Cons(car, cdr)
Base.length(c::Cons) = length(c.cdr) + 1
@inline car(c::Cons) = c.car
@inline cdr(c::Cons) = c.cdr

llfuncs = Dict(:a=>car, :d=>cdr)
for i = 1:5
    ad = keys(llfuncs)
    options = Iterators.product([ad for _ in 1:i]...)
    for seq in options
        fn = Symbol(:c, seq..., :r)
        @eval const $fn = $(foldr(∘, map(k->llfuncs[k], seq)))
    end
end


@inline assoc(d::Dict, k, v) = merge(d, Dict(k=>v))
@inline assoc(f, d::Dict, k, v) = merge(f, d, Dict(k=>v))
