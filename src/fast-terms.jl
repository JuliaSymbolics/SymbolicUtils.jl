import Base: +, -, *, /, ^
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
Base.hash(a::Add, u::UInt64) = hash(a.coeff, hash(a.dict, u))
Base.isequal(a::Add, b::Add) = isequal(a.coeff, b.coeff) && isequal(a.dict, b.dict)

function Base.show(io::IO, a::Add)
    print_coeff = !iszero(a.coeff)
    print_coeff && print(io, a.coeff)

    for (i, (k, v)) in enumerate(a.dict)
        if (i == 1 && print_coeff) || i != 1
            print(io, " + ")
        end
        print(io, v, k)
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
+(a::Number, b::Symbolic) = Add(a, make_add_dict(1, b))
+(a::Symbolic, b::Number) = Add(b, make_add_dict(1, a))
function +(a::Symbolic, b::Symbolic)
    if a isa Add
        return a + Add(0, make_add_dict(1, b))
    elseif b isa Add
        return b + a
    end
    Add(0, make_add_dict(1, a, b))
end
+(a::Add, b::Add) = Add(a.coeff + b.coeff, _merge(+, a.dict, b.dict, filter=iszero))
+(a::Number, b::Add) = iszero(a) ? b : Add(a, make_add_dict(1, b))
+(b::Add, a::Number) = iszero(a) ? b : Add(a, make_add_dict(1, b))
-(a::Add) = Add(-a.coeff, mapvalues(-, a.dict))
-(a::Symbolic) = Add(0, make_add_dict(-1, a))
-(a::Add, b::Add) = Add(a.coeff - b.coeff, _merge(-, a.dict, b.dict, filter=iszero))
-(a::Symbolic, b::Symbolic) = a + (-b)

"""
    Mul(coeff, dict)

Represents coeff * (key1 ^ val1) * (key2 ^ val2) * ....

where coeff is a non-symbolic number.
"""
struct Mul{X, T, D} <: Symbolic{X}
    coeff::T
    dict::D
end
function Base.show(io::IO, a::Mul)
    print_coeff = !isone(a.coeff)
    print_coeff && print(io, a.coeff)

    for (i, (k, v)) in enumerate(a.dict)
        if (i == 1 && print_coeff) || i != 1
            print(io, " * ")
        end
        if isone(v)
            print(io, k)
        else
            print(io, k, "^", v)
        end
    end
end
Mul(a,b) = Mul{Number, typeof(a), typeof(b)}(a,b)
Base.hash(m::Mul, u::UInt64) = hash(m.coeff, hash(m.dict, u))
Base.isequal(a::Mul, b::Mul) = isequal(a.coeff, b.coeff) && isequal(a.dict, b.dict)

*(a::Symbolic, b::Symbolic) = Mul(1, Dict(a=>1, b=>1))
*(a::Mul, b::Mul) = Mul(a.coeff * b.coeff, _merge(*, a.dict, b.dict, filter=iszero))
*(a::Number, b::Symbolic) = iszero(a) ? a : isone(a) ? b : Mul(a, Dict(b=>1))
*(b::Symbolic, a::Number) = iszero(a) ? a : isone(a) ? b : Mul(a, Dict(b=>1))

"""
    Pow(base, exp)

Represents base^exp, a lighter version of Mul(1, Dict(base=>exp))
"""
struct Pow{X, B, E} <: Symbolic{X}
    base::B
    exp::E
end
Pow(a,b) = Pow{Number, typeof(a), typeof(b)}(a,b)

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

^(a::Symbolic, b) = Pow(a, b)
function ^(a::Mul, b::Number)
    Mul(a.coeff ^ b, mapvalues((_, v) -> v^b, a.dict))
end

function mapvalues(f, d::Dict)
    d = copy(a.dict)
    for (k, v) in d
        d[k] = f(k, v)
    end
    d
end
