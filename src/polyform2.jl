const GlobalMappings = WeakKeyDict() # Key: mapping, value: weakref of the first mapping

import SIMDPolynomials

struct Poly{T, S<:SIMDPolynomials.MPoly} <: Symbolic{T}
    p::S
    mapping::Vector{Any}
end

SymbolicUtils.istree(p::Poly) = true
SymbolicUtils.operation(p::Poly) = (+)
SymbolicUtils.arguments(p::Poly) = map(x->PTerm(x.p, p.mapping), SIMDPolynomials.terms(p.p))

struct PTerm{T, S<:SIMDPolynomials.Term} <: Symbolic{T}
    p::S
    mapping::Vector{Any}
end
SymbolicUtils.istree(p::PTerm) = true
SymbolicUtils.operation(p::PTerm) = *

function SymbolicUtils.arguments(p::PTerm)
    pows = (var ^ exp for (var, exp) in zip(p.mappings, SIMDPolynomials.exps(p.monomial)) if !iszero(exp))
    isone(p.coeff) ? [pows...] : [p.coeff, pows...]
end

# @syms a b c
#
# x1 = a + b
# x2 = a + b # x1 === x2, because `+` does the check and realizes it is the same
# sin(x1) + sin(x2) # sin(x1) === sin(x2)
# 2sin(a + b)
#
# x = a + b
# y = b + c
# [x0, x1] -> [a, b]
# [x0, x1] -> [b, c]
#
# x + y --> a + 2b + c -> x0, x1, x2
#
# [x0, x1, x2] # monomial variables
# [a, b, c] # symbolic variables



function +(a::SN_EC, b::SN_EC)
    if a isa Add
        coeff, dict = makeadd(1, 0, b)
        T = promote_symtype(+, symtype(a), symtype(b))
        return Add(add_t(a,b), a.coeff + coeff, _merge(+, a.dict, dict, filter=_iszero))
    elseif b isa Add
        return b + a
    end
    Add(add_t(a,b), makeadd(1, 0, a, b)...)
end

+(a::Number, b::SN_EC) = Add(add_t(a,b), makeadd(1, a, b)...)

+(a::SN_EC, b::Number) = Add(add_t(a,b), makeadd(1, b, a)...)

+(a::SN_EC) = a

+(a::Add, b::Add) = Add(add_t(a,b),
                        a.coeff + b.coeff,
                        _merge(+, a.dict, b.dict, filter=_iszero))

+(a::Number, b::Add) = iszero(a) ? b : Add(add_t(a,b), a + b.coeff, b.dict)

+(b::Add, a::Number) = iszero(a) ? b : Add(add_t(a,b), a + b.coeff, b.dict)

-(a::Add) = Add(sub_t(a), -a.coeff, mapvalues((_,v) -> -v, a.dict))

-(a::SN_EC) = Add(sub_t(a), makeadd(-1, 0, a)...)

-(a::Add, b::Add) = Add(sub_t(a,b),
                        a.coeff - b.coeff,
                        _merge(-, a.dict, b.dict, filter=_iszero))

-(a::SN_EC, b::SN_EC) = a + (-b)

-(a::Number, b::SN_EC) = a + (-b)

-(a::SN_EC, b::Number) = a + (-b)

*(a::SN_EC) = a

function *(a::SN_EC, b::SN_EC)
    # Always make sure Div wraps Mul
    if a isa Div && b isa Div
        Div(a.num * b.num, a.den * b.den)
    elseif a isa Div
        Div(a.num * b, a.den)
    elseif b isa Div
        Div(a * b.num, b.den)
    else
        Mul(mul_t(a,b), makemul(1, a, b)...)
    end
end

*(a::Mul, b::Mul) = Mul(mul_t(a, b),
                        a.coeff * b.coeff,
                        _merge(+, a.dict, b.dict, filter=_iszero))

function *(a::Number, b::SN_EC)
    if iszero(a)
        a
    elseif isone(a)
        b
    elseif b isa Div
        Div(a*b.num, b.den)
    elseif b isa Add
        # 2(a+b) -> 2a + 2b
        T = promote_symtype(+, typeof(a), symtype(b))
        Add(T, b.coeff * a, Dict(k=>v*a for (k, v) in b.dict))
    else
        Mul(mul_t(a, b), makemul(a, b)...)
    end
end

*(a::SN_EC, b::Number) = b * a

\(a::SN_EC, b::Union{Number, SN_EC}) = b / a

\(a::Number, b::SN_EC) = b / a

/(a::SN_EC, b::Number) = (b isa Integer ? 1//b : inv(b)) * a

//(a::Union{SN_EC, Number}, b::SN_EC) = a / b

//(a::SN_EC, b::T) where {T <: Number} = (one(T) // b) * a

^(a::SN_EC, b) = Pow(a, b)

^(a::SN_EC, b::SN_EC) = Pow(a, b)

^(a::Number, b::SN_EC) = Pow(a, b)

function ^(a::Mul, b::Number)
    coeff = unstable_pow(a.coeff, b)
    Mul(promote_symtype(^, symtype(a), symtype(b)),
        coeff, mapvalues((k, v) -> b*v, a.dict))
end

function *(a::Mul, b::Pow)
    if b.exp isa Number
        Mul(mul_t(a, b),
            a.coeff, _merge(+, a.dict, Base.ImmutableDict(b.base=>b.exp), filter=_iszero))
    else
        Mul(mul_t(a, b),
            a.coeff, _merge(+, a.dict, Base.ImmutableDict(b=>1), filter=_iszero))
    end
end

*(a::Pow, b::Mul) = b * a