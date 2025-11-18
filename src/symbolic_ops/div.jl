@noinline function throw_bad_div_shape(x, y)
    throw(ArgumentError("""
    Arguments have invalid shapes for division - found shapes $x and $y.
    """))
end

@noinline function throw_vecdiv(x, y)
    throw(ArgumentError("""
    When dividing a vector, the denominator must be a scalar, vector or column matrix. \
    Found arguments with shapes $x and $y.
    """))
end

@noinline function throw_scalardiv(x, y)
    throw(ArgumentError("""
    When dividing a scalar, the denominator must be a scalar or vector. Found arguments \
    with shapes $x and $y.
    """))
end

# S = Scalar, * = Any, V = Vector, M = Matrix
# * / S -> *
# S / V -> (1, length(B))
# S / M -> ERR
# V / V -> (length(A), length(B))
# V / M -> (length(A), size(B, 1))    ; size(B, 2) == 1
# M / V -> ERR
# M / M -> (size(A, 1), size(B, 1))   ; size(A, 2) == size(B, 2)
function promote_shape(::typeof(/), sha::ShapeT, shb::ShapeT)
    @nospecialize sha shb
    ndims_a = _ndims_from_shape(sha)
    ndims_b = _ndims_from_shape(shb)
    if sha isa Unknown && shb isa Unknown
        ndims_a <= 2 || throw_bad_div_shape(sha, shb)
        ndims_b <= 2 || throw_bad_div_shape(sha, shb)
        ndims_a != 2 || ndims_b != 1 || throw_bad_dims(sha, shb)
        # either we get a matrix or the operation errors
        return Unknown(2)
    elseif sha isa Unknown && shb isa ShapeVecT
        ndims_b == 0 && return sha
        ndims_a <= 2 || throw_bad_div_shape(sha, shb)
        ndims_b <= 2 || throw_bad_div_shape(sha, shb)
        ndims_a != 1 || (ndims_b == 1 || length(shb[2]) == 1) || throw_vecdiv(sha, shb)
        ndims_a != 2 || ndims_b != 1 || throw_bad_dims(sha, shb)
        return Unknown(2)
    elseif sha isa ShapeVecT && shb isa Unknown
        ndims_a <= 2 || throw_bad_div_shape(sha, shb)
        ndims_b <= 2 || throw_bad_div_shape(sha, shb)
        ndims_a != 0 || ndims_b <= 1 || throw_scalardiv(sha, shb)
        ndims_a != 2 || ndims_b != 1 || throw_bad_dims(sha, shb)
        return Unknown(2)
    elseif sha isa ShapeVecT && shb isa ShapeVecT
        ndims_b == 0 && return sha
        ndims_a <= 2 || throw_bad_div_shape(sha, shb)
        ndims_b <= 2 || throw_bad_div_shape(sha, shb)
        if ndims_a == 0
            ndims_b == 1 && return ShapeVecT((1:1, shb[1]))
            throw_scalardiv(sha, shb)
        elseif ndims_a == 1
            ndims_b == 1 || length(shb[2]) == 1 || throw_vecdiv(sha, shb)
            return ShapeVecT((sha[1], shb[1]))
        else
            # ndims_a == 2
            ndims_b == 1 && throw_bad_div_shape(sha, shb)
            length(sha[2]) == length(shb[2]) || throw_bad_div_shape(sha, shb)
            return ShapeVecT((sha[1], shb[1]))
        end
    end
    _unreachable()
end

function _fslash_worker(::Type{T}, a, b) where {T}
    if !_numeric_or_arrnumeric_symtype(a) || !_numeric_or_arrnumeric_symtype(b)
        throw(MethodError(/, (a, b)))
    end
    type = promote_symtype(/, symtype(a), symtype(b))
    newshape = promote_shape(/, shape(a), shape(b))
    Div{T}(a, b, false; type, shape = newshape)
end

function /(a::Union{S,Number,AbstractArray{<:Number}}, b::S) where {S <: NonTreeSym}
    _fslash_worker(vartype(S), a, b)
end
function /(a::AbstractArray{S}, b::S) where {S <: NonTreeSym}
    _fslash_worker(vartype(S), Const{vartype(S)}(a), b)
end

function /(a::S, b::Union{Number,AbstractArray{<:Number}}) where {S <: NonTreeSym}
    _fslash_worker(vartype(S), a, b)
end
function /(a::S, b::AbstractArray{S}) where {S <: NonTreeSym}
    _fslash_worker(vartype(S), a, Const{vartype(S)}(b))
end

function //(a::Union{S,Number,AbstractArray{<:Number}}, b::S) where {S <: NonTreeSym}
    if !_rational_or_arrrational_symtype(a) || !_rational_or_arrrational_symtype(b)
        throw(MethodError(//, (a, b)))
    end
    _fslash_worker(vartype(S), a, b)
end
function //(a::AbstractArray{S}, b::S) where {S <: NonTreeSym}
    a = Const{vartype(S)}(a)
    if !_rational_or_arrrational_symtype(a) || !_rational_or_arrrational_symtype(b)
        throw(MethodError(//, (a, b)))
    end
    _fslash_worker(vartype(S), a, b)
end

function //(a::S, b::Union{Number,AbstractArray{<:Number}}) where {S <: NonTreeSym}
    if !_rational_or_arrrational_symtype(a) || !_rational_or_arrrational_symtype(b)
        throw(MethodError(//, (a, b)))
    end
    _fslash_worker(vartype(S), a, b)
end
function //(a::S, b::AbstractArray{S}) where {S <: NonTreeSym}
    b = Const{vartype(S)}(b)
    if !_rational_or_arrrational_symtype(a) || !_rational_or_arrrational_symtype(b)
        throw(MethodError(//, (a, b)))
    end
    _fslash_worker(vartype(S), a, b)
end

@noinline function throw_bad_dims(x, y)
    throw(ArgumentError("""
    Both arguments to \\ must have <= 2 dimensions. Found arguments with shapes $x and $y.
    """))
end

@noinline function throw_scalar_rhs(x, y)
    throw(ArgumentError("""
    The second argument to \\ cannot be a scalar if the first argument is an array. Found
    arguments with shapes $x and $y.
    """))
end

@noinline function throw_first_dim_different(x, y)
    throw(ArgumentError("""
    The length of the first dimension of both arguments to \\ must be identical. Found
    arguments with shapes $x and $y.
    """))
end

# S = Scalar, * = Any, V = Vector, M = Matrix
# S \ * -> *
# V \ S -> ERR
# V \ V -> S                        ; len(A) == len(B)
# V \ M -> (1, shape(B, 2))         ; len(A) == size(B, 1)
# M \ S -> ERR
# M \ V -> (size(A, 2))             ; size(A, 1) == length(B)
# M \ M -> (size(A, 2), size(B, 2)) ; size(A, 1) == size(B, 1)
function promote_shape(::typeof(\), sha::ShapeT, shb::ShapeT)
    @nospecialize sha shb
    ndims_a = _ndims_from_shape(sha)
    ndims_b = _ndims_from_shape(shb)
    if sha isa Unknown && shb isa Unknown
        sha.ndims <= 2 || throw_bad_dims(sha, shb)
        shb.ndims <= 2 || throw_bad_dims(sha, shb)
        sha.ndims == -1 && return Unknown(-1)
        shb.ndims == -1 && return Unknown(-1)
        sha.ndims == 1 && shb.ndims == 1 && return ShapeVecT()
        return shb
    elseif sha isa Unknown && shb isa ShapeVecT
        sha.ndims <= 2 || throw_bad_dims(sha, shb)
        length(shb) <= 2 || throw_bad_dims(sha, shb)
        length(shb) == 0 && throw_scalar_rhs(sha, shb)
        sha.ndims == -1 && return Unknown(-1)
        sha.ndims == 1 && ndims_b == 1 && return ShapeVecT()
        sha.ndims == 1 && ndims_b == 2 && return ShapeVecT((1:1, shb[2]))
        sha.ndims == 2 && return Unknown(ndims_b)
        _unreachable()
    elseif sha isa ShapeVecT && shb isa Unknown
        shb.ndims == -1 && return Unknown(-1)
        ndims_a == 0 && return shb
        ndims_a <= 2 || throw_bad_dims(sha, shb)
        shb.ndims <= 2 || throw_bad_dims(sha, shb)
        ndims_a == 1 && shb.ndims == 1 && return ShapeVecT()
        ndims_a == 1 && shb.ndims == 2 && return shb
        ndims_a == 2 && shb.ndims == 1 && return ShapeVecT((sha[1],))
        ndims_a == 2 && shb.ndims == 2 && return shb
        _unreachable()
    elseif sha isa ShapeVecT && shb isa ShapeVecT
        ndims_a == 0 && return shb
        ndims_b == 0 && throw_scalar_rhs(sha, shb)
        length(sha[1]) == length(shb[1]) || throw_first_dim_different(sha, shb)
        ndims_a <= 2 || throw_bad_dims(sha, shb)
        ndims_b <= 2 || throw_bad_dims(sha, shb)
        if ndims_a == 1 && ndims_b == 1
            return ShapeVecT()
        elseif ndims_a == 1 && ndims_b == 2
            return ShapeVecT((1:1, shb[2]))
        elseif ndims_a == 2 && ndims_b == 1
            return ShapeVecT((sha[2],))
        elseif ndims_a == 2 && ndims_b == 2
            return ShapeVecT((sha[2], shb[2]))
        end
        _unreachable()
    end
    _unreachable()
end

function _bslash_worker(::Type{T}, a, b) where {T}
    if !_numeric_or_arrnumeric_symtype(a) || !_numeric_or_arrnumeric_symtype(b)
        throw(MethodError(\, (a, b)))
    end
    if isconst(a) || isconst(b)
        return Const{T}(unwrap_const(a) \ unwrap_const(b))
    end
    sha = shape(a)
    type = promote_symtype(\, symtype(a), symtype(b))
    newshape = promote_shape(\, shape(a), shape(b))
    if is_array_shape(newshape) || is_array_shape(sha)
        # Scalar \ Anything == Anything / Scalar
        return Term{T}(\, ArgsT{T}((a, b)); type, shape = newshape)
    else
        return Div{T}(b, a, false; type, shape = newshape)
    end
end

function \(a::Union{S,Number,AbstractArray{<:Number}}, b::S) where {S <: NonTreeSym}
    _bslash_worker(vartype(S), a, b)
end
function \(a::T, b::Union{Number, <:AbstractArray{<:Number}}) where {T <: NonTreeSym}
    _bslash_worker(vartype(T), a, b)
end
function \(a::AbstractArray{S}, b::S) where {S <: NonTreeSym}
    a = Const{vartype(S)}(a)
    _bslash_worker(vartype(S), a, b)
end
function \(a::T, b::AbstractArray{T}) where {T <: NonTreeSym}
    b = Const{vartype(T)}(b)
    _bslash_worker(vartype(T), a, b)
end

