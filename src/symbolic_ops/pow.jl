@noinline function throw_matmatpow(x, y)
    throw(ArgumentError(LazyString(
        "Cannot raise matrix to matrix power -",
        " tried to raise array of shape ", x,
        " to array of shape ", y, ".")))
end

@noinline function throw_nonmatbase(x)
    throw(ArgumentError(LazyString("Matrices are the only arrays that can be raised to a power. Found array of shape ", x, ".")))
end

@noinline function throw_nonmatexp(x)
    throw(ArgumentError(LazyString("Matrices are the only arrays that can be an exponent. Found array of shape ", x, ".")))
end

@noinline function throw_nonsquarebase(x)
    throw(ArgumentError(LazyString("Only square matrices can be raised to a power. Found array of shape ", x, ".")))
end

@noinline function throw_nonsquareexp(x)
    throw(ArgumentError(LazyString("Only a square matrix can be an exponent. Found array of shape ", x, ".")))
end

function promote_shape(::typeof(^), sh1::ShapeT, sh2::ShapeT)
    @nospecialize sh1 sh2
    if sh1 isa Unknown && sh2 isa Unknown
        throw_matmatpow(sh1, sh2)
    elseif sh1 isa Unknown && sh2 isa ShapeVecT
        isempty(sh2) || throw_matmatpow(sh1, sh2)
        sh1.ndims == 2 || sh1.ndims == -1 || throw_nonmatbase(sh1)
        return Unknown(2) # either the result is a matrix or the operation will error
    elseif sh1 isa ShapeVecT && sh2 isa Unknown
        isempty(sh1) || throw_matmatpow(sh1, sh2)
        sh2.ndims == 2 || sh2.ndims == -1 || throw_nonmatexp(sh2)
        return Unknown(2) # either the result is a matrix or the operation will error
    elseif sh1 isa ShapeVecT && sh2 isa ShapeVecT
        if isempty(sh1) && isempty(sh2)
            return sh1
        elseif isempty(sh1)
            length(sh2) == 2 || throw_nonmatexp(sh2)
            length(sh2[1]) == length(sh2[2]) || throw_nonsquareexp(sh2)
            return sh2
        elseif isempty(sh2)
            length(sh1) == 2 || throw_nonmatbase(sh1)
            length(sh1[1]) == length(sh1[2]) || throw_nonsquarebase(sh1)
            return sh1
        else
            throw_matmatpow(sh1, sh2)
        end
    end
end

_fits_in(::Type{BigInt}, ::Integer) = true
_fits_in(::Type{T}, x::Integer) where {T <: Integer} = typemin(T) <= x <= typemax(T)
_fits_in(::Type{Rational{T}}, x::Rational) where {T} = _fits_in(T, numerator(x)) && _fits_in(T, denominator(x))
_fits_in(::Type{Complex{T}}, x::Complex) where {T} = _fits_in(T, real(x)) && _fits_in(T, imag(x))

_int_pow_fits(c::Int, b::Integer) = (nb = 8 * sizeof(c) - 2; b <= nb && b * ndigits(c; base = 2) <= nb)
_int_pow_fits(c, b) = false

# `Int` powers wrap and `Rational{Int}` powers throw on overflow, so an exact coefficient whose
# power may not fit its type is raised in `BigInt` arithmetic. The result has the type
# `coeff ^ b` would have when it fits.
function _exact_coeff_pow(coeff::Union{Integer, Rational, Complex{<:Union{Integer, Rational}}}, b::Integer)
    fits = coeff isa Real && isone(abs(coeff)) || _int_pow_fits(coeff, b) ||
        coeff isa Rational && _int_pow_fits(numerator(coeff), b) && _int_pow_fits(denominator(coeff), b)
    fits && return coeff ^ b
    R = typeof(one(coeff) ^ b)
    r = _widen_coeff(coeff) ^ b
    return _fits_in(R, r) ? convert(R, r) : r
end
_exact_coeff_pow(coeff, b) = coeff ^ b

"""
    _radical_parts(n::Integer, e)

Write `n ^ e`, for a positive integer `n` and an integer or rational `e`, as `c * r ^ f`
and return `(c, r, f)`, where `0 <= f < 1` and `r` has no `denominator(f)`-th power
factor that `_split_perfect_power` finds. `r` is `1` when the power is rational.
"""
function _radical_parts(@nospecialize(n::Integer), @nospecialize(e::Union{Integer, Rational}))
    # split out the common case by hand; everything else is a dynamic dispatch
    n isa Int && e isa Rational{Int} && return _radical_parts_kernel(n, e)
    return _radical_parts_kernel(n, e)
end

function _radical_parts_kernel(n::Integer, e::Union{Integer, Rational})
    k = floor(Int, e)
    f = e - k
    c = iszero(k) ? one(n) : k > 0 ? big(n) ^ k : 1 // big(n) ^ (-k)
    iszero(f) && return _narrow(c), 1, f
    s, r = _split_perfect_power(n, denominator(f))
    isone(s) || (c *= big(s) ^ numerator(f))
    return _narrow(c), _narrow(r), f
end

_is_radical_base(@nospecialize(n)) = n isa Integer && !(n isa Bool) && n > 0
_is_radical_exp(@nospecialize(e)) = e isa Rational && !isone(denominator(e))

# The canonical form of `n ^ e`: a rational coefficient times `r ^ f` with `0 < f < 1`.
function _const_radical(::Type{T}, n::Integer, e::Rational, type::TypeT) where {T}
    @nospecialize n e
    c, r, f = _radical_parts(n, e)
    isone(r) && return Const{T}(c)
    base = Const{T}(r)
    isone(c) && return BSImpl.Term{T}(^, ArgsT{T}((base, Const{T}(f))); type)
    return BSImpl.AddMul{T}(c, ACDict{T}(base => f), AddMulVariant.MUL; type, shape = ShapeVecT())
end

function _is_const_radical(x::BasicSymbolic)
    @match x begin
        BSImpl.Term(; f, args) => f === (^) && isconst(args[1]) && isconst(args[2]) &&
            _is_radical_base(unwrap_const(args[1])) && _is_radical_exp(unwrap_const(args[2]))
        _ => false
    end
end
_inv_const_radical(x::BasicSymbolic) = arguments(x)[1] ^ (-unwrap_const(arguments(x)[2]))

# An integer or rational to a non-integer rational power stays exact.
function _const_pow(::Type{T}, n::Union{Integer, Rational}, b::Rational, type::TypeT) where {T}
    @nospecialize n b
    iszero(n) && return Const{T}(b > 0 ? 0 : n ^ b)
    # a negative base is left unevaluated rather than throwing a `DomainError`
    n < 0 && return BSImpl.Term{T}(^, ArgsT{T}((Const{T}(n), Const{T}(b))); type)
    n isa Integer && return _const_radical(T, n, b, type)
    num = _const_radical(T, numerator(n), b, type)
    den = _const_radical(T, denominator(n), -b, type)
    return mul_worker(T, (num, den))::BasicSymbolic{T}
end

function ^(a::BasicSymbolic{T}, b::Union{AbstractArray{<:Number}, Number, BasicSymbolic{T}}) where {T <: Union{SymReal, SafeReal}}
    if !_numeric_or_arrnumeric_symtype(a) || !_numeric_or_arrnumeric_symtype(b)
        throw(MethodError(^, (a, b)))
    end
    if isconst(a)
        n = unwrap_const(a)
        eb = unwrap_const(unwrap(b))
        if _is_radical_exp(eb) && n isa Union{Integer, Rational} && !(n isa Bool)
            return _const_pow(T, n, eb, Real)
        end
        return Const{T}(^(n, b))
    end
    b = unwrap_const(unwrap(b))
    sha = shape(a)
    shb = shape(b)
    newshape = promote_shape(^, sha, shb)
    type = promote_symtype(^, symtype(a), symtype(b))
    # a root of an integer or rational is not one
    _is_radical_exp(b) && type <: Union{Integer, Rational} && (type = Real)

    if is_array_shape(sha)
        @match a begin
            BSImpl.Term(; f, args) && if f === (^) && isconst(args[1]) end => begin
                base, exp = args
                return Term{T}(^, ArgsT{T}((base, exp * b)); type, shape = newshape)
            end
            BSImpl.Term(; f) && if f === (*) end => begin
                coeff, rest = _split_arrterm_scalar_coeff(T, a)
                if _isone(coeff)
                    return Term{T}(^, ArgsT{T}((rest, Const{T}(b))); type, shape = newshape)
                end
                return ((coeff ^ b)::BasicSymbolic{T} * (rest ^ b)::BasicSymbolic{T})
            end
            _ => return Term{T}(^, ArgsT{T}((a, Const{T}(b))); type, shape = newshape)
        end
    elseif is_array_shape(shb)
        return Term{T}(^, ArgsT{T}((a, Const{T}(b))); type, shape = newshape)::BasicSymbolic{T}
    end
    if b isa Number
        iszero(b) && return one_of_vartype(T)
        isone(b) && return Const{T}(a)
    end
    if b isa Real && b < 0
        return Div{T}(1, a ^ (-b), false; type)::BasicSymbolic{T}
    end
    if b isa Number
        @match a begin
            # `(x^p)^b == x^(p*b)` for integer `b`, and for any real `b` when `0 < p <= 1`
            # since the principal argument of `x^p` then cannot wrap.
            BSImpl.Term(; f, args) && if f === (^) && isconst(args[2]) && symtype(args[2]) <: Number &&
                    (safe_isinteger(b) || b isa Real && (p = unwrap_const(args[2]); p isa Real && 0 < p <= 1)) end => begin
                base, exp = args
                exp = unwrap_const(exp) * b
                exp isa Rational && isone(denominator(exp)) && (exp = numerator(exp))
                return Const{T}(base ^ exp)
            end
            _ => nothing
        end
    end
    if b isa Number
        @match a begin
            BSImpl.AddMul(; coeff, dict, variant, shape, type) && if variant == AddMulVariant.MUL end => begin
                if safe_isinteger(b)
                    coeff = _exact_coeff_pow(coeff, b)
                    dict = copy(dict)
                    map!(Base.Fix1(*, b), values(dict))
                    if _has_const_key(dict)
                        coeff = _normalize_radicals!(T, coeff, dict)
                        return Mul{T}(coeff, dict; shape, type)
                    end
                    return BSImpl.AddMul{T}(coeff, dict, variant; shape, type)
                elseif coeff isa Real && !_isone(coeff) && !_isone(-coeff)
                    # A non-integer power does not distribute over a product (`sqrt(x*y)` is
                    # not `sqrt(x)*sqrt(y)` for negative `x`, `y`), but a positive constant
                    # factor can always be pulled out.
                    rest = Mul{T}(coeff < 0 ? -1 : 1, copy(dict); shape, type)
                    return (Const{T}(abs(coeff)) ^ b)::BasicSymbolic{T} * (rest ^ b)::BasicSymbolic{T}
                end
            end
            _ => nothing
        end
    end
    return BSImpl.Term{T}(^, ArgsT{T}((a, Const{T}(b))); type)
end

function ^(a::Union{Number, Matrix{<:Number}}, b::BasicSymbolic{T}) where {T}
    _numeric_or_arrnumeric_symtype(b) || throw(MethodError(^, (a, b)))
    isconst(b) && return Const{T}(a ^ unwrap_const(b))
    newshape = promote_shape(^, shape(a), shape(b))
    type = promote_symtype(^, symtype(a), symtype(b))
    if is_array_shape(newshape) && _isone(a)
        if newshape isa Unknown
            return Const{T}(LinearAlgebra.I)
        else
            return Const{T}(LinearAlgebra.I(length(newshape[1])))
        end
    end
    Term{T}(^, ArgsT{T}((Const{T}(a), b)); type, shape = newshape)
end
function ^(a::Matrix{BasicSymbolic{T}}, b::BasicSymbolic{T}) where {T <: Union{SafeReal, SymReal}}
    Const{T}(a) ^ b
end
function ^(a::BasicSymbolic{T}, b::Matrix{BasicSymbolic{T}}) where {T <: Union{SafeReal, SymReal}}
    a ^ Const{T}(b)
end
