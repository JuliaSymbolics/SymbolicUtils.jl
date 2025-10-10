import NaNMath
import SpecialFunctions: gamma, loggamma, erf, erfc, erfcinv, erfi, erfcx,
                         dawson, digamma, trigamma, invdigamma, polygamma,
                         airyai, airyaiprime, airybi, airybiprime, besselj0,
                         besselj1, bessely0, bessely1, besselj, bessely, besseli,
                         besselk, hankelh1, hankelh2, polygamma, beta, logbeta, expint,
                         expinti, sinint, cosint

const monadic = [deg2rad, rad2deg, transpose, asind, log1p, acsch,
                 acos, asec, acosh, acsc, cscd, log, tand, log10, csch, asinh,
                 abs2, cosh, sin, cos, atan, cospi, cbrt, acosd, acoth, acotd,
                 asecd, exp, acot, sqrt, sind, sinpi, asech, log2, tan, exp10,
                 sech, coth, asin, cotd, cosd, sinh, abs, csc, tanh, secd,
                 atand, sec, acscd, cot, exp2, expm1, atanh, gamma,
                 loggamma, erf, erfc, erfcinv, erfi, erfcx, dawson, digamma,
                 trigamma, invdigamma, polygamma, airyai, airyaiprime, airybi,
                 airybiprime, besselj0, besselj1, bessely0, bessely1, isfinite,
                 NaNMath.sin, NaNMath.cos, NaNMath.tan, NaNMath.asin, NaNMath.acos,
                 NaNMath.acosh, NaNMath.atanh, NaNMath.log, NaNMath.log2,
                 NaNMath.log10, NaNMath.lgamma, NaNMath.log1p, NaNMath.sqrt, sign,
                 signbit, ceil, floor, factorial, expint, expinti, sinint, cosint]

const diadic = [max, min, hypot, atan, NaNMath.atanh, mod, rem, copysign,
                besselj, bessely, besseli, besselk, hankelh1, hankelh2,
                polygamma, beta, logbeta, NaNMath.pow, expint]
const previously_declared_for = Set([])

const basic_monadic = [-, +]
const basic_diadic = [+, -, *, /, //, \, ^]
#######################################################

assert_like(f, T) = nothing
# a and b are objects, arguments gets recursively checked
function assert_like(f, T, a, b...)
    islike(a, T) || throw(ArgumentError("The function $f cannot be applied to $a which is not a $T-like object." *
                                        "Define `islike(::$(typeof(a)), ::Type{$T}) = true` to enable this."))
    assert_like(f, T, b...)
end

islike(a, T) = symtype(a) <: T

# TODO: keep domains tighter than this
function number_methods(T, rhs1, rhs2, options=nothing)
    exprs = []

    skip_basics = options !== nothing ? options == :skipbasics : false
    only_basics = options !== nothing ? options == :onlybasics : false
    skips = Meta.isexpr(options, [:vcat, :hcat, :vect]) ? Set(options.args) : []

    rhs2 = :($assert_like(f, Number, a, b); $rhs2)
    rhs1 = :($assert_like(f, Number, a); $rhs1)

    for f in (skip_basics ? diadic : only_basics ? basic_diadic : vcat(basic_diadic, diadic))
        nameof(f) in skips && continue
        for S in previously_declared_for
            push!(exprs, quote
                      (f::$(typeof(f)))(a::$T, b::$S) = $rhs2
                      (f::$(typeof(f)))(a::$S, b::$T) = $rhs2
                  end)
        end

        # TODO: modularize and make another macro?
        expr = quote
            (f::$(typeof(f)))(a::$T, b::$T) = $rhs2
            (f::$(typeof(f)))(a::$T, b::Real)   = $rhs2
            (f::$(typeof(f)))(a::Real, b::$T)   = $rhs2
            (f::$(typeof(f)))(a::$T, b::Number) = $rhs2
            (f::$(typeof(f)))(a::Number, b::$T) = $rhs2
        end

        push!(exprs, expr)

        # Fix method ambiguity error on NaNMath >= 1.0.2 and promotion of `Integer`s on NaNMath < 1.0.2
        if f === NaNMath.pow
            push!(exprs, :((f::$(typeof(f)))(a::$T, b::Integer) = a ^ b))
        end
    end

    for f in (skip_basics ? monadic : only_basics ? basic_monadic : vcat(basic_monadic, monadic))
        nameof(f) in skips && continue
        if f === isfinite
            push!(exprs, :((f::$(typeof(f)))(a::$T) = true))
        else
            push!(exprs, :((f::$(typeof(f)))(a::$T)   = $rhs1))
        end
    end
    push!(exprs, :(push!($previously_declared_for, $T)))
    Expr(:block, exprs...)
end

macro number_methods(T, rhs1, rhs2, options=nothing)
    number_methods(T, rhs1, rhs2, options) |> esc
end

@number_methods(BasicSymbolic{SymReal},
                Term{SymReal}(f, ArgsT{SymReal}((Const{SymReal}(a),)); type = promote_symtype(f, symtype(a))),
                Term{SymReal}(f, ArgsT{SymReal}((Const{SymReal}(a), Const{SymReal}(b))); type = promote_symtype(f, symtype(a), symtype(b))),
                skipbasics)
@number_methods(BasicSymbolic{TreeReal},
                Term{TreeReal}(f, ArgsT{TreeReal}((Const{TreeReal}(a),)); type = promote_symtype(f, symtype(a))),
                Term{TreeReal}(f, ArgsT{TreeReal}((Const{TreeReal}(a), Const{TreeReal}(b))); type = promote_symtype(f, symtype(a), symtype(b))))

for f in vcat(diadic, [+, -, *, ^, Base.add_sum, Base.mul_prod])
    @eval promote_symtype(::$(typeof(f)),
                   ::Type{T},
                   ::Type{S}) where {T <: Number, S <: Number} = promote_type(T, S)
    @eval promote_symtype(::$(typeof(f)),
                   ::Type{T},
                   ::Type{S}) where {T <: Number, S <: BigInt} = promote_type(T, Integer)
    @eval promote_symtype(::$(typeof(f)),
                   ::Type{S},
                   ::Type{T}) where {T <: Number, S <: BigInt} = promote_type(T, Integer)
    @eval promote_symtype(::$(typeof(f)),
                   ::Type{BigInt},
                   ::Type{BigInt}) = BigInt
    @eval promote_symtype(::$(typeof(f)),
                   ::Type{T},
                   ::Type{S}) where {T <: Number, S <: BigFloat} = promote_type(T, Real)
    @eval promote_symtype(::$(typeof(f)),
                   ::Type{S},
                   ::Type{T}) where {T <: Number, S <: BigFloat} = promote_type(T, Real)
    @eval promote_symtype(::$(typeof(f)),
                   ::Type{BigFloat},
                   ::Type{BigFloat}) = BigFloat
    @eval promote_symtype(::$(typeof(f)),
                   ::Type{BigInt},
                   ::Type{BigFloat}) = BigFloat
    @eval promote_symtype(::$(typeof(f)),
                   ::Type{BigFloat},
                   ::Type{BigInt}) = BigFloat
    @eval promote_symtype(::$(typeof(f)),
                   ::Type{T},
                   ::Type{S}) where {T <: Rational, S <: BigInt} = promote_type(T, Integer)
    @eval promote_symtype(::$(typeof(f)),
                   ::Type{S},
                   ::Type{T}) where {T <: Rational, S <: BigInt} = promote_type(T, Integer)
    @eval promote_symtype(::$(typeof(f)),
                   ::Type{T},
                   ::Type{S}) where {eT, T <: Rational{eT}, S <: Integer} = Real
    @eval promote_symtype(::$(typeof(f)),
                   ::Type{T},
                   ::Type{S}) where {T <: Integer, eS, S <: Rational{eS}} = Real
    @eval promote_symtype(::$(typeof(f)),
                   ::Type{T},
                   ::Type{S}) where {eT, T <: Complex{Rational{eT}}, S <: Integer} = Complex{Real}
    @eval promote_symtype(::$(typeof(f)),
                   ::Type{T},
                   ::Type{S}) where {T <: Integer, eS, S <: Complex{Rational{eS}}} = Complex{Real}
    @eval promote_symtype(::$(typeof(f)),
                   ::Type{T},
                   ::Type{BigInt}) where {eT, T <: Complex{Rational{eT}}} = Complex{Real}
    @eval promote_symtype(::$(typeof(f)),
                   ::Type{BigInt},
                   ::Type{S}) where {eS, S <: Complex{Rational{eS}}} = Complex{Real}
end

for f in [/, \]
    @eval promote_symtype(::$(typeof(f)),
                   ::Type{T},
                   ::Type{S}) where {T <: Number, S <: Number} = promote_type(T, S)
    @eval promote_symtype(::$(typeof(f)),
                   ::Type{T},
                   ::Type{S}) where {T <: Integer, S <: Integer} = Real
    @eval promote_symtype(::$(typeof(f)),
                   ::Type{T},
                   ::Type{S}) where {T <: Rational, S <: Integer} = Real
    @eval promote_symtype(::$(typeof(f)),
                   ::Type{T},
                   ::Type{S}) where {T <: Integer, S <: Rational} = Real
    @eval promote_symtype(::$(typeof(f)),
                   ::Type{T},
                   ::Type{S}) where {eT, T <: Complex{eT}, S <: Union{Integer, Rational}} = Complex{promote_type(eT, Real)}
    @eval promote_symtype(::$(typeof(f)),
                   ::Type{T},
                   ::Type{S}) where {T <: Union{Integer, Rational}, eS, S <: Complex{eS}} = Complex{promote_type(Real, eS)}
    @eval promote_symtype(::$(typeof(f)),
                   ::Type{T},
                   ::Type{S}) where {eT, T <: Complex{eT}, eS, S <: Complex{eS}} = Complex{promote_type(promote_type(eT, eS), Real)}
end

function promote_symtype(::typeof(+), ::Type{T}, ::Type{S}) where {eT <: Number, N, T <: AbstractArray{eT, N}, eS <: Number, S <: AbstractArray{eS, N}}
    return Array{promote_symtype(+, eT, eS), N}
end

function promote_symtype(::typeof(*), ::Type{T}, ::Type{S}) where {eT <: Number, T <: AbstractMatrix{eT}, eS <: Number, S <: AbstractVecOrMat{eS}}
    return Array{promote_symtype(*, eT, eS), ndims(S)}
end

function promote_symtype(::typeof(*), ::Type{T}, ::Type{S}) where {eT <: Number, N, T <: AbstractArray{eT, N}, S <: Number}
    return Array{promote_symtype(*, eT, S), N}
end

function promote_symtype(::typeof(*), ::Type{T}, ::Type{S}) where {T <: Number, eS <: Number, N, S <: AbstractArray{eS, N}}
    return Array{promote_symtype(*, T, eS), N}
end

function promote_symtype(::typeof(^), ::Type{T}, ::Type{S}) where {T <: Number, E <: Number, S <: AbstractMatrix{E}}
    Matrix{promote_type(T, E)}
end
function promote_symtype(::typeof(^), ::Type{T}, ::Type{S}) where {E <: Number, T <: AbstractMatrix{E}, S <: Integer}
    T
end
_complex(::Type{Number}) = Number
_complex(::Type{T}) where {T} = complex(T)
function promote_symtype(::typeof(^), ::Type{T}, ::Type{S}) where {E <: Number, T <: AbstractMatrix{E}, S <: Number}
    Matrix{_complex(promote_type(E, S))}
end

function promote_symtype(::typeof(\), ::Type{T}, ::Type{S}) where {T <: Number, eS <: Number, N, S <: AbstractArray{eS, N}}
    Array{promote_symtype(/, eS, T), N}
end

function promote_symtype(::typeof(\), ::Type{T}, ::Type{S}) where {eT <: Number, T <: AbstractVector{eT}, eS <: Number, S <: AbstractVector{eS}}
    promote_symtype(/, eS, eT)
end

function promote_symtype(::typeof(\), ::Type{T}, ::Type{S}) where {eT <: Number, T <: AbstractVecOrMat{eT}, eS <: Number, S <: AbstractMatrix{eS}}
    Matrix{promote_symtype(/, eS, eT)}
end

function promote_symtype(::typeof(\), ::Type{T}, ::Type{S}) where {eT <: Number, T <: AbstractMatrix{eT}, eS <: Number, S <: AbstractVector{eS}}
    Vector{promote_symtype(/, eS, eT)}
end

# we don't actually care about specifically making the Mat/Vec case error because
# `promote_shape` handles it with a much nicer error message than we can give here.
function promote_symtype(::typeof(/), ::Type{T}, ::Type{S}) where {eT <: Number, T <: AbstractVecOrMat{eT}, eS <: Number, S <: AbstractVecOrMat{eS}}
    Matrix{promote_symtype(/, eT, eS)}
end

function promote_symtype(::typeof(/), ::Type{T}, ::Type{S}) where {T <: Number, eS <: Number, S <: AbstractVector{eS}}
    Matrix{promote_symtype(/, T, eS)}
end

function promote_symtype(::typeof(/), ::Type{T}, ::Type{S}) where {eT <: Number, N, T <: AbstractArray{eT, N}, S <: Number}
    Array{promote_symtype(/, eT, S), N}
end

promote_symtype(::typeof(identity), ::Type{T}) where {T} = T
promote_shape(::typeof(identity), @nospecialize(sh::ShapeT)) = sh

function _sequential_promote(::Type{T}, ::Type{S}, Ts...) where {T, S}
    _sequential_promote(promote_type(T, S), Ts...)
end
_sequential_promote(::Type{T}) where {T} = T


function promote_symtype(::typeof(hvncat), ::Type{NTuple{N, Int}}, Ts...) where {N}
    return Array{_sequential_promote(Ts...), N}
end

promote_symtype(::typeof(rem2pi), T::Type{<:Number}, mode) = T

@noinline function _throw_array(f, shs...)
    throw(ArgumentError("Invalid shapes for $f: $shs."))
end

for f in diadic
    f === NaNMath.pow && continue
    @eval function promote_shape(::$(typeof(f)), sh1::ShapeT, sh2::ShapeT)
        @nospecialize sh1 sh2
        is_array_shape(sh1) && _throw_array($f, sh1, sh2)
        is_array_shape(sh2) && _throw_array($f, sh1, sh2)
        return ShapeVecT()
    end
end
promote_shape(::typeof(NaNMath.pow), @nospecialize(shs::ShapeT...)) = promote_shape(^, shs...)

for f in monadic
    if f === log || f === NaNMath.log
        @eval function promote_shape(::$(typeof(f)), sh::ShapeT)
            @nospecialize sh
            if sh isa Unknown
                sh.ndims == -1 && return sh
                sh.ndims == 2 && return sh
            elseif sh isa ShapeVecT
                length(sh) == 0 && return sh
                length(sh) == 2 && return sh
            end
            _throw_array($f, sh)
        end
    else
        @eval function promote_shape(::$(typeof(f)), sh::ShapeT)
            @nospecialize sh
            is_array_shape(sh) && _throw_array($f, sh)
            return ShapeVecT()
        end
    end
end

error_f_symbolic(f, T) = error("$f is not defined for $T.")

function promote_shape(::typeof(rem2pi), sha::ShapeT, shb::ShapeT)
    is_array_shape(sha) && _throw_array(rem2pi, sha, shb)
    ShapeVecT()
end
function Base.rem2pi(x::BasicSymbolic{T}, mode::Base.RoundingMode) where {T}
    type = symtype(x)
    type <: Number || error_f_symbolic(rem2pi, type)
    return Term{T}(rem2pi, ArgsT{T}((x, Const{T}(mode))); type)
end

promote_symtype(::typeof(inv), ::Type{T}) where {T <: Number} = promote_symtype(/, T, T)
function promote_symtype(::typeof(inv), ::Type{T}) where {eT <: Number, T <: AbstractMatrix{eT}}
    Matrix{promote_symtype(/, eT, eT)}
end
function promote_symtype(::typeof(inv), ::Type{T}) where {T}
    error("Cannot call `inv` on $T.")
end
function promote_shape(::typeof(inv), sh::ShapeT)
    @nospecialize sh
    if sh isa Unknown
        sh.ndims == -1 && return sh
        sh.ndims == 2 && return sh
    elseif sh isa ShapeVecT
        length(sh) == 0 && return sh
        length(sh) == 2 && return ShapeVecT((sh[2], sh[1]))
    end
    _throw_array(inv, sh)
end

# Specially handle inv and literal pow
function Base.inv(x::BasicSymbolic{T}) where {T}
    sh = shape(x)
    type = promote_symtype(inv, symtype(x))
    if is_array_shape(sh)
        return Term{T}(inv, ArgsT{T}((x,)); type = type, shape = sh)
    else
        return x ^ (-1)
    end
end
function Base.literal_pow(::typeof(^), x::BasicSymbolic{T}, ::Val{p}) where {T, p}
    _numeric_or_arrnumeric_symtype(x) || error_f_symbolic(^, symtype(x))
    return Const{T}(x ^ p)
end
function promote_symtype(::typeof(Base.literal_pow), _, ::Type{T}, ::Type{Val{S}}) where{T<:Number,S}
    return promote_symtype(^, T, typeof(S))
end

promote_symtype(::Any, T) = promote_type(T, Real)
for f in monadic
    if f in [sign, signbit, ceil, floor, factorial]
        continue
    end
    @eval promote_symtype(::$(typeof(f)), T::Type{<:Number}) = promote_type(T, Real)
end

for f in [identity, one, zero, *, +, -]
    @eval promote_symtype(::$(typeof(f)), T::Type{<:Number}) = T
end

promote_symtype(::typeof(Base.real), ::Type{T}) where {eT, T <: Complex{eT}} = eT
promote_symtype(::typeof(Base.real), ::Type{T}) where {T <: Real} = T
for f in [real, imag, conj]
    @eval function promote_shape(::typeof($f), sh::ShapeT)
        @nospecialize sh
        return sh
    end
end
function Base.real(s::BasicSymbolic{T}) where {T}
    islike(s, Real) && return s
    @match s begin
        BSImpl.Const(; val) => Const{T}(real(val))
        BSImpl.Term(; f, args) && if f === complex && length(args) == 2 end => args[1]
        _ => Term{T}(real, ArgsT{T}((s,)); type = Real)
    end
end
promote_symtype(::typeof(Base.conj), T::Type{<:Number}) = T
function Base.conj(s::BasicSymbolic{T}) where {T}
    eltype(symtype(s)) <: Real && return s
    @match s begin
        BSImpl.Const(; val) => Const{T}(conj(val))
        BSImpl.Term(; f, args, type, shape) && if f === complex && length(args) == 2 end => begin
            BSImpl.Term{T}(f, ArgsT{T}(args[1], -args[2]); type, shape)
        end
        _ => Term{T}(conj, ArgsT{T}((s,)); type = symtype(s), shape = shape(s))
    end
end
promote_symtype(::typeof(Base.imag), ::Type{T}) where {eT, T <: Complex{eT}} = eT
promote_symtype(::typeof(Base.imag), ::Type{T}) where {T <: Real} = T
function Base.imag(s::BasicSymbolic{T}) where {T}
    islike(s, Real) && return zero_of_vartype(T)
    @match s begin
        BSImpl.Const(; val) => Const{T}(imag(val))
        BSImpl.Term(; f, args) && if f === complex && length(args) == 2 end => args[2]
        _ => Term{T}(imag, ArgsT{T}((s,)); type = Real)
    end
end

promote_symtype(::typeof(adjoint), ::Type{T}) where {T <: Number} = T
function promote_symtype(::typeof(adjoint), ::Type{T}) where {eT <: Number, T <: AbstractVecOrMat{eT}}
    Matrix{eT}
end

@noinline function _throw_adjont_vec_or_mat(sh)
    throw(ArgumentError("""
    `adjoint` is only applicable to vectors and matrices - found argument of shape $sh.
    """))
end

function promote_shape(::typeof(adjoint), sh::ShapeT)
    ndims = _ndims_from_shape(sh)
    ndims > 2 && _throw_adjont_vec_or_mat(sh)
    if sh isa Unknown
        ndims == 0 && _throw_adjont_vec_or_mat(sh)
        return Unknown(2)
    elseif sh isa ShapeVecT
        ndims == 0 && return ShapeVecT()
        return ShapeVecT((ndims == 1 ? (1:1) : sh[2], sh[1]))
    end
end

function Base.adjoint(s::BasicSymbolic{T}) where {T}
    @match s begin
        BSImpl.Const(; val) => return Const{T}(adjoint(val))
        _ => nothing
    end
    sh = shape(s)
    stype = symtype(s)
    if is_array_shape(sh)
        type = promote_symtype(adjoint, stype)
        newsh = promote_shape(adjoint, sh)
        return Term{T}(adjoint, ArgsT{T}((s,)); type, shape = newsh)
    elseif stype <: Real
        return s
    else
        return conj(s)
    end
end


## Booleans

# binary ops that return Bool
for (f, Domain) in [(==) => Number, (!=) => Number,
                    (<=) => Real,   (>=) => Real,
                    (isless) => Real,
                    (<) => Real,   (> ) => Real,
                    (& ) => Bool,   (| ) => Bool,
                    xor => Bool]
    @eval begin
        promote_symtype(::$(typeof(f)), ::Type{<:$Domain}, ::Type{<:$Domain}) = Bool
        function (::$(typeof(f)))(a::BasicSymbolic{T}, b::$Domain) where {T}
            if !(symtype(a) <: $Domain)
                throw(MethodError($f, (a, b)))
            end
            Term{T}($f, ArgsT{T}((a, Const{T}(b))); type = Bool)
        end
        function (::$(typeof(f)))(a::$Domain, b::BasicSymbolic{T}) where {T}
                if !(symtype(b) <: $Domain)
                    throw(MethodError($f, (a, b)))
                end
                Term{T}($f, ArgsT{T}((Const{T}(a), b)); type = Bool)
        end
        function (::$(typeof(f)))(a::BasicSymbolic{T}, b::BasicSymbolic{T}) where {T}
                if !(symtype(b) <: $Domain) || !(symtype(a) <: $Domain)
                    throw(MethodError($f, (a, b)))
                end
                Term{T}($f, ArgsT{T}((a, b)); type = Bool)
        end
    end
end

for f in [!, ~]
    @eval begin
        promote_symtype(::$(typeof(f)), ::Type{<:Bool}) = Bool
        function (::$(typeof(f)))(s::BasicSymbolic{T}) where {T}
            type = symtype(s)
            if type !== Bool
                throw(MethodError(!, (s,)))
            end
            Term{T}(!, ArgsT{T}((s,)); type)
        end
    end
end


# An ifelse node
function Base.ifelse(_if::BasicSymbolic{T}, _then, _else) where {T}
    type = Union{symtype(_then), symtype(_else)}
    Term{T}(ifelse, ArgsT{T}((_if, _then, _else)); type)
end
promote_symtype(::typeof(ifelse), ::Type{Bool}, ::Type{T}, ::Type{S}) where {T,S} = Union{T, S}
function promote_symtype(::typeof(ifelse), ::Type{B}, ::Type{T}, ::Type{S}) where {B, T,S}
    throw(ArgumentError("Condition of `ifelse` must be a `Bool`"))
end

# Array-like operations
Base.IndexStyle(::Type{<:BasicSymbolic}) = Base.IndexCartesian()
function _size_from_shape(shape::ShapeT)
    @nospecialize shape
    if shape isa Unknown
        return shape
    else
        return Tuple(map(length, shape))
    end
end
Base.size(x::BasicSymbolic) = _size_from_shape(shape(x))
function Base.size(x::BasicSymbolic, i::Integer)
    sh = shape(x)
    if sh isa Unknown
        return sh
    elseif sh isa ShapeVecT
        return length(sh[i])
    end
    _unreachable()
end
Base.axes(x::BasicSymbolic) = Tuple(shape(x))
Base.axes(x::BasicSymbolic, i::Integer) = shape(x)[i]
function _length_from_shape(sh::ShapeT)
    @nospecialize sh
    if sh isa Unknown
        return sh
    else
        len = 1
        for dim in sh
            len *= length(dim)
        end
        return len
    end
end
Base.length(x::BasicSymbolic) = _length_from_shape(shape(x))
function _ndims_from_shape(sh::ShapeT)
    @nospecialize sh
    if sh isa Unknown
        return sh.ndims
    else
        return length(sh)
    end
end
Base.ndims(x::BasicSymbolic) = _ndims_from_shape(shape(x))
Base.broadcastable(x::BasicSymbolic) = is_array_shape(shape(x)) ? x : Ref(x)
function Base.eachindex(x::BasicSymbolic)
    sh = shape(x)
    if sh isa Unknown
        throw(ArgumentError("Indices of variable $x with unknown shape $sh are not defined."))
    end
    CartesianIndices(Tuple(sh))
end

"""
    $TYPEDEF

An iterator that produces [`StableIndex`](@ref) values representing all possible
multi-dimensional indices for a given shape in a type-stable, allocation-efficient manner.

This type is used to iterate over multi-dimensional index spaces where each
dimension can have its own range (stored in `sh`). The iterator produces all
combinations of indices in column-major order, similar to `CartesianIndices`,
but with better type stability and allocation characteristics.

This is similar to `CartesianIndices` for symbolic arrays, but avoids type-instability due
to the type parameters of `CartesianIndices` being uninferrable. Note that iterator
iterates over multidimensional indices, but is not a multidimensional iterator. In other
words, `collect`ing this iterator will return a vector regardless of the number of
dimensions it iterates over.

# Fields
$TYPEDFIELDS

# Examples
```julia
sh = ShapeVecT([1:2, 1:3])
indices = StableIndices(sh)
for idx in indices
    # idx is a StableIndex with values like [1,1], [1,2], [1,3], [2,1], [2,2], [2,3]
end
```

# See also
- [`StableIndex`](@ref): The index type produced by this iterator.
- [`stable_eachindex`](@ref): Convenience function that returns a `StableIndices` iterator for a symbolic array.
"""
struct StableIndices
    """
    A small vector of `UnitRange{Int}` values, one for each dimension, defining the range
    of valid indices for that dimension.
    """
    sh::ShapeVecT
end

Base.length(x::StableIndices) = prod(length, x.sh; init = 1)
Base.eltype(::Type{StableIndices}) = StableIndex

function Base.iterate(x::StableIndices)
    idx = SmallV{Int}()
    resize!(idx, length(x.sh))
    for i in eachindex(x.sh)
        idx[i] = first(x.sh[i])
    end
    idx = StableIndex(idx)
    return idx, idx
end
function Base.iterate(x::StableIndices, st::StableIndex)
    idxs = st.idxs
    buffer = copy(idxs)
    i = 1
    N = length(x.sh)
    while i <= N
        buffer[i] += 1
        buffer[i] > last(x.sh[i]) || break
        buffer[i] = first(x.sh[i])
        i += 1
    end
    i <= N || return nothing
    idxs = StableIndex(buffer)
    return idxs, idxs
end
function Base.getindex(x::StableIndices, idx::Integer)
    buffer = SmallV{Int}()
    N = length(x.sh)
    idx -= 1
    for i in 1:N
        push!(buffer, idx % length(x.sh[i]) + first(x.sh[i]))
        idx ÷= length(x.sh[i])
    end
    return StableIndex(buffer)
end

"""
    $TYPEDSIGNATURES

Returns a type-stable iterator over all indices of a symbolic array `x`.

This function provides an efficient, allocation-friendly way to iterate over
multi-dimensional symbolic arrays. Unlike `Base.eachindex`, which returns
`CartesianIndices` with type parameters that may be uninferrable for symbolic
arrays, `stable_eachindex` returns a [`StableIndices`](@ref) iterator that
produces [`StableIndex`](@ref) values in a fully type-stable manner.

Note that the returned iterator does not match the shape of `x`. In other
words, `collect(stable_eachindex(x))` will be a vector regardless of the shape
of `x`.

# Arguments
- `x::BasicSymbolic`: A symbolic array expression with a known concrete shape.

# Returns
- `StableIndices`: An iterator that yields `StableIndex` values for each position in the array.

# Throws
- This function assumes `x` has a concrete shape (i.e., `shape(x)` is a `ShapeVecT`,
  not `Unknown`). If the shape is unknown, it will error.

# Examples
```julia
using SymbolicUtils

# Create a symbolic 2×3 matrix
@variables x[1:2, 1:3]

# Iterate over all indices in a type-stable manner
for idx in stable_eachindex(x)
    println("Index: ", idx, " -> Value: ", x[idx])
end

# Compare with regular eachindex
for idx in eachindex(x)  # Returns CartesianIndices
    println("Index: ", idx, " -> Value: ", x[idx])
end
```

# See also
- [`StableIndices`](@ref): The iterator type returned by this function
- [`StableIndex`](@ref): The index type produced by `StableIndices`
- `Base.eachindex`: The standard Julia function for iterating over array indices
"""
function stable_eachindex(x::BasicSymbolic)
    StableIndices(shape(x)::ShapeVecT)
end
function Base.collect(x::BasicSymbolic)
    scalarize(x, Val{true}())
end
function Base.iterate(x::BasicSymbolic)
    sh = shape(x)
    is_array_shape(sh) || return x, nothing
    idxs = eachindex(x)
    idx, state = iterate(idxs)
    return x[idx], (idxs, state)
end
function Base.iterate(x::BasicSymbolic, _state)
    _state === nothing && return nothing
    idxs, state = _state
    innerstate = iterate(idxs, state)
    innerstate === nothing && return nothing
    idx, state = innerstate
    return x[idx], (idxs, state)
end
function Base.isempty(x::BasicSymbolic)
    sh = shape(x)
    if sh isa Unknown
        return false
    elseif sh isa ShapeVecT
        return _length_from_shape(sh) == 0
    end
    _unreachable()
end

promote_symtype(::Type{CartesianIndex}, xs...) = CartesianIndex{length(xs)}
promote_symtype(::Type{CartesianIndex{N}}, xs::Vararg{T, N}) where {T, N} = CartesianIndex{N}
function promote_shape(::Type{CartesianIndex}, xs::ShapeT...)
    @nospecialize xs
    @assert all(!is_array_shape, xs)
    return ShapeVecT((1:length(xs),))
end
function promote_shape(::Type{CartesianIndex{N}}, xs::Vararg{ShapeT, N}) where {N}
    @nospecialize xs
    @assert all(!is_array_shape, xs)
    return ShapeVecT((1:length(xs),))
end
function Base.CartesianIndex(x::BasicSymbolic{T}, xs::BasicSymbolic{T}...) where {T}
    @assert symtype(x) <: Integer
    @assert all(x -> symtype(x) <: Integer, xs)
    type = promote_symtype(CartesianIndex, symtype(x), symtype.(xs)...)
    sh = promote_shape(CartesianIndex, shape(x), shape.(xs)...)
    BSImpl.Term{T}(CartesianIndex{length(xs) + 1}, ArgsT{T}((x, xs...)); type, shape = sh)
end

for (f, vT) in [(sign, Number), (signbit, Number), (ceil, Number), (floor, Number), (factorial, Integer)]
    @eval promote_symtype(::typeof($f), ::Type{T}) where {T <: $vT} = T
end

function promote_symtype(::typeof(clamp),
                         ::Type{T},
                         ::Type{S},
                         ::Type{R}) where {T <: Number, S <: Number, R <: Number}
    promote_type(T, S, R)
end
function promote_symtype(::typeof(clamp),
                         ::Type{T},
                         ::Type{S},
                         ::Type{R}) where {T <: AbstractVector{<:Number},
                                           S <: AbstractVector{<:Number},
                                           R <: AbstractVector{<:Number}}
    Vector{promote_type(eltype(T), eltype(S), eltype(R))}
end

function promote_shape(::typeof(clamp), sh1::ShapeT, sh2::ShapeT, sh3::ShapeT)
    @nospecialize sh1 sh2 sh3
    nd1 = _ndims_from_shape(sh1)
    nd2 = _ndims_from_shape(sh2)
    nd3 = _ndims_from_shape(sh3)
    maxd = max(nd1, nd2, nd3)
    @assert maxd <= 1
    if maxd >= 0
        @assert nd1 == -1 || nd1 == maxd
        @assert nd2 == -1 || nd2 == maxd
        @assert nd3 == -1 || nd3 == maxd
    end
    if maxd == 0
        return ShapeVecT()
    elseif sh1 isa ShapeVecT
        return ShapeVecT((1:length(sh1[1])))
    elseif sh2 isa ShapeVecT
        return ShapeVecT((1:length(sh2[1])))
    elseif sh3 isa ShapeVecT
        return ShapeVecT((1:length(sh3[1])))
    else
        return Unknown(1)
    end
end

for valT in [Number, AbstractVector{<:Number}]
    for (T1, T2, T3) in Iterators.product(Iterators.repeated((valT, :(BasicSymbolic{T})), 3)...)
        if T1 == T2 == T3 == valT
            continue
        end
        if valT != Number && T1 == T2 == T3
            continue
        end
        @eval function Base.clamp(a::$T1, b::$T2, c::$T3) where {T}
            isconst(a) && isconst(b) && isconst(c) && return Const{T}(clamp(unwrap_const(a), unwrap_const(b), unwrap_const(c)))
            sh = promote_shape(clamp, shape(a), shape(b), shape(c))
            type = promote_symtype(clamp, symtype(a), symtype(b), symtype(c))
            return BSImpl.Term{T}(clamp, ArgsT{T}((Const{T}(a), Const{T}(b), Const{T}(c))); type, shape = sh)
        end
    end
end

struct SymBroadcast{T <: SymVariant} <: Broadcast.BroadcastStyle end
Broadcast.BroadcastStyle(::Type{BasicSymbolic{T}}) where {T} = SymBroadcast{T}()
Broadcast.BroadcastStyle(::SymBroadcast{T}, ::Broadcast.BroadcastStyle) where {T} = SymBroadcast{T}()
Broadcast.BroadcastStyle(::SymBroadcast{T}, ::SymBroadcast{T}) where {T} = SymBroadcast{T}()
function Broadcast.BroadcastStyle(::SymBroadcast{T}, ::SymBroadcast{R}) where {T, R}
    throw(ArgumentError("Cannot broadcast symbolics of different `vartype`s $T and $R."))
end

mutable struct BroadcastBuffer{T}
    canonical_args::Vector{BasicSymbolic{T}}
    args::ArgsT{T}
    getindex_args::ArgsT{T}
end

BroadcastBuffer{T}() where {T} = BroadcastBuffer{T}(BasicSymbolic{T}[], ArgsT{T}(), ArgsT{T}())

function Base.empty!(bb::BroadcastBuffer)
    empty!(bb.canonical_args)
    empty!(bb.args)
    empty!(bb.getindex_args)
    return bb
end

function maybe_reallocate_getindex_buffer!(bb::BroadcastBuffer{T}, term::BasicSymbolic{T}) where {T}
    @match term begin
        BSImpl.Term(; args) && if args === bb.getindex_args end => begin
            bb.getindex_args = ArgsT{T}()
        end
        _ => empty!(bb.getindex_args)
    end
    return nothing
end
function maybe_reallocate_args_buffer!(bb::BroadcastBuffer{T}, term::BasicSymbolic{T}) where {T}
    @match term begin
        BSImpl.Term(; args) && if args === bb.args end => begin
            bb.args = ArgsT{T}()
        end
        _ => empty!(bb.args)
    end
    return nothing
end

const SYMREAL_BROADCAST_BUFFER = TaskLocalValue{BroadcastBuffer{SymReal}}(BroadcastBuffer{SymReal})
const SAFEREAL_BROADCAST_BUFFER = TaskLocalValue{BroadcastBuffer{SafeReal}}(BroadcastBuffer{SafeReal})
const TREEREAL_BROADCAST_BUFFER = TaskLocalValue{BroadcastBuffer{TreeReal}}(BroadcastBuffer{TreeReal})

broadcast_buffer(::Type{SymReal}) = SYMREAL_BROADCAST_BUFFER[]
broadcast_buffer(::Type{SafeReal}) = SAFEREAL_BROADCAST_BUFFER[]
broadcast_buffer(::Type{TreeReal}) = TREEREAL_BROADCAST_BUFFER[]

function Broadcast.copy(bc::Broadcast.Broadcasted{SymBroadcast{T}}) where {T}
    buffer = broadcast_buffer(T)
    empty!(buffer)
    _copy_broadcast!(buffer, bc)
end

function _copy_broadcast!(buffer::BroadcastBuffer{T}, bc::Broadcast.Broadcasted{SymBroadcast{T}, A, typeof(Base.literal_pow), Tuple{Base.RefValue{typeof(^)}, B, Base.RefValue{Val{N}}}}) where {T, A, B, N}
    _copy_broadcast!(buffer, Broadcast.Broadcasted{SymBroadcast{T}}(^, (bc.args[2], N), bc.axes))
end

function _copy_broadcast!(buffer::BroadcastBuffer{T}, bc::Broadcast.Broadcasted{SymBroadcast{T}}) where {T}
    offset = length(buffer.canonical_args)
    for arg in bc.args
        if arg isa Broadcast.Broadcasted
            push!(buffer.canonical_args, _copy_broadcast!(buffer, Broadcast.instantiate(arg)))
        elseif arg isa Base.RefValue
            push!(buffer.canonical_args, Const{T}(arg[]))
        else
            push!(buffer.canonical_args, Const{T}(arg))
        end
    end
    canonical_args = view(buffer.canonical_args, (offset+1):(offset+length(bc.args)))
    # Do the thing here
    ndim = length(bc.axes)
    if ndim == 0
        return maketerm(BasicSymbolic{T}, bc.f, bc.args, nothing)
    end
    subscripts = idxs_for_arrayop(T)

    args = buffer.args

    for arg in canonical_args
        sh = shape(arg)
        is_arr = is_array_shape(sh)
        if !is_arr
            push!(args, arg)
            continue
        end
        getindex_args = buffer.getindex_args
        push!(getindex_args, arg)
        if sh isa Unknown
            # unknown ndims, assume full shape
            limit = sh.ndims == -1 ? ndim : sh.ndims
            for i in 1:limit
                push!(getindex_args,  length(bc.axes[i]) == 1 ? one_of_vartype(T) : subscripts[i])
            end
        elseif sh isa ShapeVecT
            for (i, (target_ax, cur_ax)) in enumerate(zip(bc.axes, sh))
                len1 = length(cur_ax)
                len2 = length(target_ax)
                push!(getindex_args, len1 < len2 ? Const{T}(first(cur_ax)) : subscripts[i])
            end
        end
        # manual construction is faster than calling `getindex`
        indexed_arg = Term{T}(getindex, getindex_args; type = eltype(symtype(arg)), shape = ShapeVecT())
        maybe_reallocate_getindex_buffer!(buffer, indexed_arg)
        push!(args, indexed_arg)
    end
    output_idxs = OutIdxT{T}()
    for (i, ax) in enumerate(bc.axes)
        push!(output_idxs, length(ax) == 1 ? 1 : subscripts[i])
    end
    expr = maketerm(BasicSymbolic{T}, bc.f, args, nothing)
    maybe_reallocate_args_buffer!(buffer, expr)
    args = buffer.args
    push!(args, Const{T}(bc.f))
    for arg in canonical_args
        push!(args, Const{T}(arg))
    end
    sh = ShapeVecT()
    for ax in bc.axes
        push!(sh, 1:length(ax))
    end
    type = Array{eltype(symtype(expr)), ndim}
    term = Term{T}(broadcast, args; type, shape = sh)
    maybe_reallocate_args_buffer!(buffer, term)
    resize!(buffer.canonical_args, length(buffer.canonical_args) - length(bc.args))

    return BSImpl.ArrayOp{T}(output_idxs, expr, +, term; type, shape = sh)
end

@noinline function _throw_unequal_lengths(x, y)
    throw(ArgumentError("""
    Arguments must have equal lengths. Got arguments with shapes $x and $y.
    """))
end

function promote_shape(::typeof(LinearAlgebra.dot), sha::ShapeT, shb::ShapeT)
    @nospecialize sha shb
    if sha isa ShapeVecT && shb isa ShapeVecT
        _length_from_shape(sha) == _length_from_shape(shb) 
    end
    ShapeVecT()
end

promote_symtype(::typeof(LinearAlgebra.dot), ::Type{T}, ::Type{S}) where {T <: Number, S <: Number} = promote_type(T, S)
promote_symtype(::typeof(LinearAlgebra.dot), ::Type{T}, ::Type{S}) where {eT, T <: AbstractArray{eT}, eS, S <: AbstractArray{eS}} = promote_symtype(LinearAlgebra.dot, eT, eS)

function LinearAlgebra.dot(x::BasicSymbolic{T}, y::BasicSymbolic{T}) where {T}
    shx = shape(x)
    if is_array_shape(shx)
        sh = promote_shape(LinearAlgebra.dot, shx, shape(y))
        type = promote_symtype(LinearAlgebra.dot, symtype(x), symtype(y))
        BSImpl.Term{T}(LinearAlgebra.dot, ArgsT{T}((x, y)); type, shape = sh)
    else
        conj(x) * y
    end
end
function LinearAlgebra.dot(x::Number, y::BasicSymbolic{T}) where {T}
    x = unwrap(x)
    promote_shape(LinearAlgebra.dot, ShapeVecT(), shape(y))
    return conj(x) * y
end
function LinearAlgebra.dot(x::BasicSymbolic{T}, y::Number) where {T}
    y = unwrap(y)
    promote_shape(LinearAlgebra.dot, shape(x), ShapeVecT())
    return conj(x) * y
end
function LinearAlgebra.dot(x::AbstractArray, y::BasicSymbolic{T}) where {T}
    LinearAlgebra.dot(Const{T}(x), y)
end
function LinearAlgebra.dot(x::BasicSymbolic{T}, y::AbstractArray) where {T}
    LinearAlgebra.dot(x, Const{T}(y))
end

promote_symtype(::typeof(LinearAlgebra.det), ::Type{T}) where {T <: Number} = T
promote_symtype(::typeof(LinearAlgebra.det), ::Type{T}) where {eT, T <: AbstractMatrix{eT}} = eT

@noinline function _throw_not_matrix(x)
    throw(ArgumentError("Expected argument to be a matrix, got argument of shape $x."))
end

function promote_shape(::typeof(LinearAlgebra.det), sh::ShapeT)
    @nospecialize sh
    if sh isa Unknown
        sh.ndims == -1 || sh.ndims == 2 || _throw_not_matrix(sh)
    elseif sh isa ShapeVecT
        length(sh) == 0 || length(sh) == 2 || _throw_not_matrix(sh)
    end
    return ShapeVecT()
end

function LinearAlgebra.det(A::BasicSymbolic{T}) where {T}
    type = promote_symtype(LinearAlgebra.det, symtype(A))
    sh = promote_shape(LinearAlgebra.det, shape(A))
    BSImpl.Term{T}(LinearAlgebra.det, ArgsT{T}((A,)); type, shape = sh)
end

struct Mapper{F}
    f::F
end

function (f::Mapper)(xs...)
    map(f.f, xs...)
end

function promote_symtype(f::Mapper, ::Type{T}, Ts...) where {eT, N, T <: AbstractArray{eT, N}}
    Array{promote_symtype(f.f, eT, eltype.(Ts)...), N}
end

function promote_shape(::Mapper, shs::ShapeT...)
    @nospecialize shs
    @assert allequal(Iterators.map(_size_from_shape, shs))
    sz = _size_from_shape(shs[1])
    if sz isa Unknown
        sz.ndims == -1 && error("Cannot `map` when first argument has unknown `ndims`.")
        return sz
    end
    return ShapeVecT((:).(1, sz))
end

function _map(::Type{T}, f, xs...) where {T}
    f = Mapper(f)
    xs = Const{T}.(xs)
    type = promote_symtype(f, symtype.(xs)...)
    sh = promote_shape(f, shape.(xs)...)
    nd = ndims(sh)
    term = BSImpl.Term{T}(f, ArgsT{T}(xs); type, shape = sh)
    idxsym = idxs_for_arrayop(T)
    idxs = OutIdxT{T}()
    sizehint!(idxs, nd)
    for i in 1:nd
        push!(idxs, idxsym[i])
    end
    idxs = ntuple(Base.Fix1(getindex, idxsym), nd)

    indexed = ntuple(Val(length(xs))) do i
        xs[i][idxs...]
    end
    exp = BSImpl.Term{T}(f.f, ArgsT{T}(indexed); type = eltype(type), shape = ShapeVecT())
    return BSImpl.ArrayOp{T}(idxs, exp, +, term; type = type, shape = sh)
end

function Base.map(f::BasicSymbolic{T}, xs...) where {T}
    _map(T, f, xs...)
end
function Base.map(f::BasicSymbolic{T}, x::AbstractArray, xs...) where {T}
    _map(T, f, x, xs...)
end

for fT in [Any, :(BasicSymbolic{T})]
    @eval function Base.map(f::$fT, x::BasicSymbolic{T}, xs...) where {T}
        _map(T, f, x, xs...)
    end
    for x1T in [Any, :(BasicSymbolic{T})]
        @eval function Base.map(f::$fT, x1::$x1T, x::BasicSymbolic{T}, xs...) where {T}
            _map(T, f, x1, x, xs...)
        end
    end
end

macro map_methods(T, arg_f, result_f)
    quote
        function (::$(typeof(Base.map)))(f, x::$T, xs...)
            $result_f($map(f, $arg_f(x), xs...))
        end
        function (::$(typeof(Base.map)))(f::$BasicSymbolic, x::$T, xs...)
            $result_f($map(f, $arg_f(x), xs...))
        end
        function (::$(typeof(Base.map)))(f, x1, x::$T, xs...)
            $result_f($map(f, x1, $arg_f(x), xs...))
        end
        function (::$(typeof(Base.map)))(f::$BasicSymbolic{V}, x1::$BasicSymbolic{V}, x::$T, xs...) where {V}
            $result_f($map(f, x1, $arg_f(x), xs...))
        end
    end |> esc
end

struct Mapreducer{F, R}
    f::F
    reduce::R
end

function (f::Mapreducer)(xs...)
    mapreduce(f.f, f.reduce, xs...)
end

function promote_symtype(f::Mapreducer, ::Type{T}, Ts...) where {eT, N, T <: AbstractArray{eT, N}}
    mappedT = promote_symtype(f.f, eT, eltype.(Ts)...)
    return promote_symtype(f.reduce, mappedT, mappedT)
end

function promote_shape(f::Mapreducer, shs::ShapeT...)
    @nospecialize shs
    promote_shape(Mapper(f.f), shs...)
    return ShapeVecT()
end

function __index_args(::Type{T}, ::Val{N}, xs...) where {T, N}
    idxsym = idxs_for_arrayop(T)
    inner_idxs = ntuple(Base.Fix1(getindex, idxsym), Val{N}())
    indexer = let xs = xs, inner_idxs = inner_idxs
        function __indexer(i)
            xs[i][inner_idxs...]
        end
    end
    ntuple(indexer, Val(length(xs)))
end

function _mapreduce(::Type{T}, f, red, xs...) where {T}
    f = Mapreducer(f, red)
    xs = Const{T}.(xs)
    type = promote_symtype(f, symtype.(xs)...)
    sh = promote_shape(f, shape.(xs)...)
    term = BSImpl.Term{T}(f, ArgsT{T}(xs); type, shape = sh)
    idxs = OutIdxT{T}()

    indexed = __index_args(T, Val(ndims(xs[1])), xs...)::NTuple{length(xs), BasicSymbolic{T}}
    exp = BSImpl.Term{T}(f.f, ArgsT{T}(indexed); type = eltype(type), shape = ShapeVecT())
    return BSImpl.ArrayOp{T}(idxs, exp, red, term; type = type, shape = sh)
end

for (Tf, Tr) in Iterators.product([:(BasicSymbolic{T}), Any], [:(BasicSymbolic{T}), Any])
    if Tf != Any || Tr != Any
        @eval function Base.mapreduce(f::$Tf, red::$Tr, xs...) where {T}
            return _mapreduce(T, f, red, xs...)
        end
        @eval function Base.mapreduce(f::$Tf, red::$Tr, x::AbstractArray, xs...) where {T}
            return _mapreduce(T, f, red, x, xs...)
        end
    end
    @eval function Base.mapreduce(f::$Tf, red::$Tr, x::BasicSymbolic{T}, xs...) where {T}
        _mapreduce(T, f, red, x, xs...)
    end
    for x1T in [Any, :(BasicSymbolic{T})]
        @eval function Base.mapreduce(f::$Tf, red::$Tr, x1::$x1T, x::BasicSymbolic{T}, xs...) where {T}
            _mapreduce(T, f, red, x1, x, xs...)
        end
    end
end

function _mapreduce_method(fT, redT, xTs...; splat = true, kw...)
    args = [:(f::$fT), :(red::$redT)]
    for (i, xT) in enumerate(xTs)
        name = Symbol(:x, i)
        push!(args, :($name::$xT))
    end
    splat && push!(args, :(xs::Vararg))
    EL.codegen_ast(EL.JLFunction(; name = :(::$(typeof(mapreduce))), args, kw...))
end

macro mapreduce_methods(T, arg_f, result_f)
    result = Expr(:block)

    Ts = [:($BasicSymbolic{T}), Any]
    for (Tf, Tred) in Iterators.product(Ts, Ts)
        whereparams = if Tf != Any || Tred != Any
            [:T]
        else
            nothing
        end

        body = :($result_f($mapreduce(f, red, $arg_f(x1))))
        push!(result.args, _mapreduce_method(Tf, Tred, T; splat = false, body, whereparams))
        body = :($result_f($mapreduce(f, red, $arg_f(x1), xs...)))
        push!(result.args, _mapreduce_method(Tf, Tred, T; body, whereparams))
        body = :($result_f($mapreduce(f, red, x1, $arg_f(x2), xs...)))
        push!(result.args, _mapreduce_method(Tf, Tred, Any, T; body, whereparams))
        push!(result.args, _mapreduce_method(Tf, Tred, BasicSymbolic, T; body, whereparams))
    end
    return esc(result)
end

function operator_to_term(::Operator, ex::BasicSymbolic{T}) where {T}
    return ex
end

function Base.Symbol(ex::BasicSymbolic{T}) where {T}
    @match ex begin
        BSImpl.Term(; f) && if f isa Operator end => Symbol(string(operator_to_term(f, ex)::BasicSymbolic{T}))
        _ => Symbol(string(ex))
    end
end

function promote_symtype(::typeof(in), ::Type{T}, ::Type{S}) where {T, S}
    return Bool
end
function promote_shape(::typeof(in), sha::ShapeT, shb::ShapeT)
    @nospecialize sha shb
    @assert is_array_shape(shb) || throw(ArgumentError("Symbolic `in` requires an array as the second argument."))
    return ShapeVecT()
end

for T1 in [Real, :(BasicSymbolic{T})], T2 in [AbstractArray, :(BasicSymbolic{T})]
    if !(T1 isa Expr) && !(T2 isa Expr)
        continue
    end
    @eval function Base.in(a::$T1, b::$T2) where {T}
        sh = promote_shape(in, shape(a), shape(b))
        return BSImpl.Term{T}(in, ArgsT{T}((Const{T}(a), Const{T}(b))); type = Bool, shape = sh)
    end
end

function promote_symtype(::typeof(issubset), ::Type{T}, ::Type{S}) where {T <: AbstractArray, S <: AbstractArray}
    Bool
end
function promote_shape(::typeof(issubset), sha::ShapeT, shb::ShapeT)
    @nospecialize sha shb
    @assert is_array_shape(sha) || throw(ArgumentError("Symbolic `issubset` requires arrays as both arguments."))
    @assert is_array_shape(shb) || throw(ArgumentError("Symbolic `issubset` requires arrays as both arguments."))
    return ShapeVecT()
end

for T1 in [AbstractArray, :(BasicSymbolic{T})], T2 in [AbstractArray, :(BasicSymbolic{T})]
    if !(T1 isa Expr) && !(T2 isa Expr)
        continue
    end
    @eval function Base.issubset(a::$T1, b::$T2) where {T}
        sh = promote_shape(issubset, shape(a), shape(b))
        return BSImpl.Term{T}(issubset, ArgsT{T}((Const{T}(a), Const{T}(b))); type = Bool, shape = sh)
    end
end

for f in [union, intersect]
    @eval function promote_symtype(::$(typeof(f)), ::Type{T},
                             ::Type{S}) where {eT, T <: AbstractArray{eT}, eS,
                                               S <: AbstractArray{eS}}
        return Vector{promote_type(eT, eS)}
    end
    @eval function promote_shape(::$(typeof(f)), sha::ShapeT, shb::ShapeT)
        @nospecialize sha shb
        @assert is_array_shape(sha) || throw(ArgumentError("Symbolic `$($f)` requires arrays as both arguments."))
        @assert is_array_shape(shb) || throw(ArgumentError("Symbolic `$($f)` requires arrays as both arguments."))
        return Unknown(1)
    end
    for T1 in [AbstractArray, :(BasicSymbolic{T})], T2 in [AbstractArray, :(BasicSymbolic{T})]
        if !(T1 isa Expr) && !(T2 isa Expr)
            continue
        end
        @eval function (::$(typeof(f)))(a::$T1, b::$T2) where {T}
            sh = promote_shape($f, shape(a), shape(b))
            type = promote_type($f, symtype(a), symtype(b))
            return BSImpl.Term{T}($f, ArgsT{T}((Const{T}(a), Const{T}(b))); type, shape = sh)
        end
    end
end

promote_symtype(::typeof(complex), ::Type{T}) where {T <: Real} = Complex{T}
promote_symtype(::typeof(complex), ::Type{T}) where {T <: Number} = T
function promote_symtype(::typeof(complex), ::Type{T}, ::Type{S}) where {T <: Real, S <: Real}
    Complex{promote_type(T, S)}
end

function promote_symtype(::typeof(binomial), ::Type{T}, ::Type{S}) where {T <: Number,
                                                                          S <: Integer}
    return T
end
function promote_shape(::typeof(binomial), sha::ShapeT, shb::ShapeT)
    @nospecialize sha shb
    is_array_shape(sha) && _throw_array(sha)
    is_array_shape(shb) && _throw_array(shb)

    return ShapeVecT()
end

for T1 in [Number, :(BasicSymbolic{T})], T2 in [Integer, :(BasicSymbolic{T})]
    if !(T1 isa Expr) && !(T2 isa Expr)
        continue
    end
    @eval function Base.binomial(a::$T1, b::$T2) where {T}
        sh = promote_shape(binomial, shape(a), shape(b))
        return BSImpl.Term{T}(binomial, ArgsT{T}((Const{T}(a), Const{T}(b))); type = symtype(a), shape = sh)
    end
end
