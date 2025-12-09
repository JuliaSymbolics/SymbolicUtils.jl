@noinline function throw_matmatpow(x, y)
    throw(ArgumentError("""
    Cannot raise matrix to matrix power - tried to raise array of shape $x to array of \
    shape $y.
    """))
end

@noinline function throw_nonmatbase(x)
    throw(ArgumentError("""
    Matrices are the only arrays that can be raised to a power. Found array of shape $x.
    """))
end

@noinline function throw_nonmatexp(x)
    throw(ArgumentError("""
    Matrices are the only arrays that can be an exponent. Found array of shape $x.
    """))
end

@noinline function throw_nonsquarebase(x)
    throw(ArgumentError("""
    Only square matrices can be raised to a power. Found array of shape $x.
    """))
end

@noinline function throw_nonsquareexp(x)
    throw(ArgumentError("""
    Only a square matrix can be an exponent. Found array of shape $x.
    """))
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

function ^(a::BasicSymbolic{T}, b::Union{AbstractArray{<:Number}, Number, BasicSymbolic{T}}) where {T <: Union{SymReal, SafeReal}}
    if !_numeric_or_arrnumeric_symtype(a) || !_numeric_or_arrnumeric_symtype(b)
        throw(MethodError(^, (a, b)))
    end
    isconst(a) && return Const{T}(^(unwrap_const(a), b))
    b = unwrap_const(unwrap(b))
    sha = shape(a)
    shb = shape(b)
    newshape = promote_shape(^, sha, shb)
    type = promote_symtype(^, symtype(a), symtype(b))

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
            BSImpl.Term(; f, args) && if f === (^) && isconst(args[2]) && symtype(args[2]) <: Number end => begin
                base, exp = args
                base, exp = arguments(a)
                exp = unwrap_const(exp)
                return Const{T}(base ^ (exp * b))
            end
            BSImpl.Term(; f, args) && if f === sqrt && (safe_isinteger(b) && Int(b) % 2 == 0 || b isa Rational && numerator(b)%2 == 0) end => begin
                exp = safe_isinteger(b) ? (Int(b) // 2) : (b::Rational // 2)
                return Const{T}(args[1] ^ exp)
            end
            BSImpl.Term(; f, args) && if f === cbrt && (safe_isinteger(b) && Int(b) % 3 == 0 || b isa Rational && numerator(b)%3 == 0) end => begin
                exp = safe_isinteger(b) ? (Int(b) // 3) : (b::Rational // 3)
                return Const{T}(args[1] ^ exp)
            end
            _ => nothing
        end
    end
    if b isa Number
        @match a begin
            BSImpl.AddMul(; coeff, dict, variant, shape, type) && if variant == AddMulVariant.MUL end => begin
                if coeff isa Real && coeff < 0 && !safe_isinteger(b)
                    coeff = (-coeff) ^ b
                    newmul = BSImpl.AddMul{T}(-1, dict, variant; shape, type)
                    # newpow = Term{T}(^, ArgsT{T}((newmul, b)); shape, type)
                    if _isone(coeff)
                        return Term{T}(^, ArgsT{T}((newmul, b)); shape, type)
                    else
                        return BSImpl.AddMul{T}(coeff, ACDict{T}(newmul => b), AddMulVariant.MUL; shape, type)
                    end
                    # return mul_worker(T, (coeff, newpow))
                else
                    coeff = coeff ^ b
                    dict = copy(dict)
                    map!(Base.Fix1(*, b), values(dict))
                    return BSImpl.AddMul{T}(coeff, dict, variant; shape, type)
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
