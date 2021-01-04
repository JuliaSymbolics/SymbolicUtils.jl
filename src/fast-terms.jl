import Base: +, -, *, /, ^

const SN = Symbolic{<:Number}
"""
    Add(coeff, dict)

Represents coeff + (key1 * val1) + (key2 * val2) + ...

where coeff and the vals are non-symbolic numbers.

"""
struct Add{X, T, D} <: Symbolic{X}
    coeff::T
    dict::D
end

function Add(coeff, dict)
    if isempty(dict)
        return coeff
    end
    Add{Number, typeof(coeff), typeof(dict)}(coeff,dict)
end

symtype(a::Add{X}) where {X} = X

istree(a::Add) = true

operation(a::Add) = +

arguments(a::Add) = vcat(a.coeff, [v*k for (k,v) in a.dict])

Base.hash(a::Add, u::UInt64) = hash(a.coeff, hash(a.dict, u))

Base.isequal(a::Add, b::Add) = isequal(a.coeff, b.coeff) && isequal(a.dict, b.dict)

function Base.show(io::IO, a::Add)
    print_coeff = !iszero(a.coeff)
    print_coeff && print(io, a.coeff)

    for (i, (k, v)) in enumerate(a.dict)
        if (i == 1 && print_coeff) || i != 1
            print(io, " + ")
        end
        if isone(v)
            print(io, k)
        else
            print(io, v, k)
        end
    end
end

"""
    make_add_dict(sign, xs...)

Any Muls inside an Add should always have a coeff of 1
and the key (in Add) should instead be used to store the actual coefficient
"""
function make_add_dict(sign, xs...)
    d = Dict{Any, Number}()
    for x in xs
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
    d
end

+(a::Number, b::SN) = Add(a, make_add_dict(1, b))
+(a::SN, b::Number) = Add(b, make_add_dict(1, a))
-(a::Number, b::SN) = a + (-b)
-(a::SN, b::Number) = a + (-b)

function +(a::SN, b::SN)
    if a isa Add
        return a + Add(0, make_add_dict(1, b))
    elseif b isa Add
        return b + a
    end
    Add(0, make_add_dict(1, a, b))
end

+(a::Add, b::Add) = Add(a.coeff + b.coeff, _merge(+, a.dict, b.dict, filter=iszero))

+(a::Number, b::Add) = iszero(a) ? b : Add(a + b.coeff, b.dict)

+(b::Add, a::Number) = iszero(a) ? b : Add(a + b.coeff, b.dict)

-(a::Add) = Add(-a.coeff, mapvalues(-, a.dict))

-(a::SN) = Add(0, make_add_dict(-1, a))

-(a::Add, b::Add) = Add(a.coeff - b.coeff, _merge(-, a.dict, b.dict, filter=iszero))

-(a::SN, b::SN) = a + (-b)

"""
    Mul(coeff, dict)

Represents coeff * (key1 ^ val1) * (key2 ^ val2) * ....

where coeff is a non-symbolic number.
"""
struct Mul{X, T, D} <: Symbolic{X}
    coeff::T
    dict::D
end

function Mul(a,b)
    isempty(b) && return a
    if isone(a) && length(b) == 1
        pair = first(b)
        if isone(last(pair)) # first value
            return first(pair)
        else
            return Pow(first(pair), last(pair))
        end
    else
        Mul{Number, typeof(a), typeof(b)}(a,b)
    end
end

symtype(a::Mul{X}) where {X} = X

istree(a::Mul) = true

operation(a::Mul) = *

arguments(a::Mul) = vcat(a.coeff, [k^v for (k,v) in a.dict])

Base.hash(m::Mul, u::UInt64) = hash(m.coeff, hash(m.dict, u))

Base.isequal(a::Mul, b::Mul) = isequal(a.coeff, b.coeff) && isequal(a.dict, b.dict)

function Base.show(io::IO, a::Mul)
    print_coeff = !isone(a.coeff)
    print_coeff && print(io, a.coeff)

    for (i, (k, v)) in enumerate(a.dict)
        if (i == 1 && print_coeff) || i != 1
            print(io, " * ")
        end
        if isone(v)
            if !(k isa Sym)
                print(io, "(", k, ")")
            else
                print(io, k)
            end
        else
            if !(k isa Sym)
                print(io, "(", k, ")^", v)
            else
                print(io, k, "^", v)
            end
        end
    end
end

"""
make_mul_dict(xs...)
"""
function make_mul_coeff_dict(sign, coeff, xs...; d=Dict{Any, Number}())
    for x in xs
        if x isa Pow
            d[x.base] = sign * x.exp + get(d, x.base, 0)
        elseif x isa Mul
            coeff *= x.coeff
            dict = isone(sign) ? x.dict : mapvalues((_,v)->sign*v, x.dict)
            d = _merge(+, d, dict, filter=iszero)
        else
            k = x
            v = sign + get(d, x, 0)
            if iszero(v)
                delete!(d, k)
            else
                d[k] = v
            end
        end
    end
    coeff, d
end

*(a::SN, b::SN) = Mul(make_mul_coeff_dict(1, 1, a, b)...)

*(a::Mul, b::Mul) = Mul(a.coeff * b.coeff, _merge(+, a.dict, b.dict, filter=iszero))

*(a::Number, b::SN) = iszero(a) ? a : isone(a) ? b : Mul(make_mul_coeff_dict(1,a, b)...)

*(b::SN, a::Number) = iszero(a) ? a : isone(a) ? b : Mul(make_mul_coeff_dict(1,a, b)...)

function /(a::Union{SN,Number}, b::SN)
    a * Mul(make_mul_coeff_dict(-1, 1, b)...)
end

\(a::SN, b::SN) = b / a

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
    iszero(b) && return 1
    isone(b) && return a
    Pow{Number, typeof(a), typeof(b)}(a,b)
end

symtype(a::Pow{X}) where {X} = X

istree(a::Pow) = true

operation(a::Pow) = ^

arguments(a::Pow) = [a.base, a.exp]

Base.hash(p::Pow, u::UInt) = hash(p.exp, hash(p.base, u))

Base.isequal(p::Pow, b::Pow) = isequal(p.base, b.base) && isequal(p.exp, b.exp)

function Base.show(io::IO, p::Pow)
    k, v = p.base, p.exp
    if !(k isa Sym)
        print(io, "(", k, ")^", v)
    else
        print(io, k, "^", v)
    end
end

^(a::SN, b) = Pow(a, b)

function ^(a::Mul, b::Number)
    Mul(a.coeff ^ b, mapvalues((k, v) -> b*v, a.dict))
end

function *(a::Mul, b::Pow)
    Mul(a.coeff, _merge(+, a.dict, Base.ImmutableDict(b.base=>b.exp), filter=iszero))
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

function mapvalues(f, d1::Dict)
    d = copy(d1)
    for (k, v) in d
        d[k] = f(k, v)
    end
    d
end
