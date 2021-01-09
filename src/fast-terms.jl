import Base: +, -, *, /, \, ^

sdict(kv...) = Dict{Any, Number}(kv...)

# this cannot be Symbolic{<:Number} to make MTK Parameters work. See #155
const SN = Symbolic
"""
    Add(coeff, dict)

Represents coeff + (key1 * val1) + (key2 * val2) + ...

where coeff and the vals are non-symbolic numbers.

"""
struct Add{X, T<:Number, D} <: Symbolic{X}
    coeff::T
    dict::D
    sorted_args_cache::Ref{Any}
end

function Add(T, coeff, dict)
    if isempty(dict)
        return coeff
    elseif _iszero(coeff) && length(dict) == 1
        k,v = first(dict)
        return _isone(v) ? k : makemul(1, v, k)
    end

    Add{T, typeof(coeff), typeof(dict)}(coeff, dict, Ref{Any}(nothing))
end

symtype(a::Add{X}) where {X} = X


istree(a::Add) = true

operation(a::Add) = +

function arguments(a::Add)
    a.sorted_args_cache[] !== nothing && return a.sorted_args_cache[]
    args = sort!([v*k for (k,v) in a.dict], lt=<ₑ)
    a.sorted_args_cache[] = iszero(a.coeff) ? args : vcat(a.coeff, args)
end

Base.hash(a::Add, u::UInt64) = hash(a.coeff, hash(a.dict, u))

Base.isequal(a::Add, b::Add) = isequal(a.coeff, b.coeff) && isequal(a.dict, b.dict)

Base.show(io::IO, a::Add) = show_term(io, a)

"""
    makeadd(sign, coeff::Number, xs...)

Any Muls inside an Add should always have a coeff of 1
and the key (in Add) should instead be used to store the actual coefficient
"""
function makeadd(sign, coeff, xs...)
    d = sdict()
    for x in xs
        if x isa Number
            coeff += x
            continue
        end
        if x isa Mul
            k = Mul(1, x.dict)
            v = sign * x.coeff + get(d, k, 0)
        else
            k = x
            v = sign + get(d, x, 0)
        end
        if iszero(v)
            delete!(d, k)
        else
            d[k] = v
        end
    end
    coeff, d
end

add_t(a,b) = promote_symtype(+, symtype(a), symtype(b))
sub_t(a,b) = promote_symtype(-, symtype(a), symtype(b))
sub_t(a) = promote_symtype(-, symtype(a))

function +(a::SN, b::SN)
    if a isa Add
        coeff, dict = makeadd(1, 0, b)
        T = promote_symtype(+, symtype(a), symtype(b))
        return Add(add_t(a,b), a.coeff + coeff, _merge(+, a.dict, dict, filter=_iszero))
    elseif b isa Add
        return b + a
    end
    Add(add_t(a,b), makeadd(1, 0, a, b)...)
end

+(a::Number, b::SN) = Add(add_t(a,b), makeadd(1, a, b)...)

+(a::SN, b::Number) = Add(add_t(a,b), makeadd(1, b, a)...)

+(a::SN) = a

+(a::Add, b::Add) = Add(add_t(a,b),
                        a.coeff + b.coeff,
                        _merge(+, a.dict, b.dict, filter=_iszero))

+(a::Number, b::Add) = iszero(a) ? b : Add(add_t(a,b), a + b.coeff, b.dict)

+(b::Add, a::Number) = iszero(a) ? b : Add(add_t(a,b), a + b.coeff, b.dict)

-(a::Add) = Add(sub_t(a), -a.coeff, mapvalues((_,v) -> -v, a.dict))

-(a::SN) = Add(sub_t(a), makeadd(-1, 0, a)...)

-(a::Add, b::Add) = Add(sub_t(a,b),
                        a.coeff - b.coeff,
                        _merge(-, a.dict, b.dict, filter=_iszero))

-(a::SN, b::SN) = a + (-b)

-(a::Number, b::SN) = a + (-b)

-(a::SN, b::Number) = a + (-b)

"""
    Mul(coeff, dict)

Represents coeff * (key1 ^ val1) * (key2 ^ val2) * ....

where coeff is a non-symbolic number.
"""
struct Mul{X, T<:Number, D} <: Symbolic{X}
    coeff::T
    dict::D
    sorted_args_cache::Ref{Any}
end

function Mul(a,b)
    isempty(b) && return a
    if _isone(a) && length(b) == 1
        pair = first(b)
        if _isone(last(pair)) # first value
            return first(pair)
        else
            return Pow(first(pair), last(pair))
        end
    else
        Mul{Number, typeof(a), typeof(b)}(a,b, Ref{Any}(nothing))
    end
end

symtype(a::Mul{X}) where {X} = X

istree(a::Mul) = true

operation(a::Mul) = *

function arguments(a::Mul)
    a.sorted_args_cache[] !== nothing && return a.sorted_args_cache[]
    args = sort!([k^v for (k,v) in a.dict], lt=<ₑ)
    a.sorted_args_cache[] = isone(a.coeff) ? args : vcat(a.coeff, args)
end

Base.hash(m::Mul, u::UInt64) = hash(m.coeff, hash(m.dict, u))

Base.isequal(a::Mul, b::Mul) = isequal(a.coeff, b.coeff) && isequal(a.dict, b.dict)


Base.show(io::IO, a::Mul) = show_term(io, a)

"""
makemul(xs...)
"""
function makemul(sign, coeff, xs...; d=sdict())
    for x in xs
        if x isa Pow && x.exp isa Number
            d[x.base] = sign * x.exp + get(d, x.base, 0)
        elseif x isa Number
            coeff *= x
        elseif x isa Mul
            coeff *= x.coeff
            dict = isone(sign) ? x.dict : mapvalues((_,v)->sign*v, x.dict)
            d = _merge(+, d, dict, filter=_iszero)
        else
            k = x
            v = sign + get(d, x, 0)
            if _iszero(v)
                delete!(d, k)
            else
                d[k] = v
            end
        end
    end
    Mul(coeff, d)
end

mul_t(a,b) = promote_symtype(*, symtype(a), symtype(b))
mul_t(a) = promote_symtype(*, symtype(a))

*(a::SN) = a

*(a::SN, b::SN) = makemul(1, 1, a, b)

*(a::Mul, b::Mul) = Mul(a.coeff * b.coeff, _merge(+, a.dict, b.dict, filter=_iszero))

*(a::Number, b::SN) = iszero(a) ? a : isone(a) ? b : makemul(1,a, b)

*(b::SN, a::Number) = iszero(a) ? a : isone(a) ? b : makemul(1,a, b)

function /(a::Union{SN,Number}, b::SN)
    a * makemul(-1, 1, b)
end

\(a::SN, b::Union{Number, SN}) = b / a

\(a::Number, b::SN) = b / a

/(a::SN, b::Number) = inv(b) * a

"""
    Pow(base, exp)

Represents base^exp, a lighter version of Mul(1, Dict(base=>exp))
"""
struct Pow{X, B, E} <: Symbolic{X}
    base::B
    exp::E
end

function Pow(a,b)
    _iszero(b) && return 1
    _isone(b) && return a
    Pow{Number, typeof(a), typeof(b)}(a,b)
end

symtype(a::Pow{X}) where {X} = X

istree(a::Pow) = true

operation(a::Pow) = ^

arguments(a::Pow) = [a.base, a.exp]

Base.hash(p::Pow, u::UInt) = hash(p.exp, hash(p.base, u))

Base.isequal(p::Pow, b::Pow) = isequal(p.base, b.base) && isequal(p.exp, b.exp)

Base.show(io::IO, p::Pow) = show_term(io, p)

^(a::SN, b) = Pow(a, b)

^(a::SN, b::SN) = Pow(a, b)

^(a::Number, b::SN) = Pow(a, b)

function ^(a::Mul, b::Number)
    Mul(a.coeff ^ b, mapvalues((k, v) -> b*v, a.dict))
end

function *(a::Mul, b::Pow)
    if b.exp isa Number
        Mul(a.coeff, _merge(+, a.dict, Base.ImmutableDict(b.base=>b.exp), filter=_iszero))
    else
        Mul(a.coeff, _merge(+, a.dict, Base.ImmutableDict(b=>1), filter=_iszero))
    end
end

*(a::Pow, b::Mul) = b * a

function _merge(f, d, others...; filter=x->false)
    acc = copy(d)
    for other in others
        for (k, v) in other
            if haskey(acc, k)
                v = f(acc[k], v)
            end
            if filter(v)
                delete!(acc, k)
            else
                acc[k] = v
            end
        end
    end
    acc
end

function mapvalues(f, d1::AbstractDict)
    d = copy(d1)
    for (k, v) in d
        d[k] = f(k, v)
    end
    d
end

function similarterm(p::Union{Mul, Add, Pow}, f, args)
    if f === (+)
        Add(makeadd(1, 0, args...)...)
    elseif f == (*)
        makemul(1, 1, args...)
    elseif f == (^)
        Pow(args...)
    else
        f(args...)
    end
end
