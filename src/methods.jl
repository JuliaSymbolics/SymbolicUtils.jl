import NaNMath
import SpecialFunctions: gamma, loggamma, erf, erfc, erfcinv, erfi, erfcx,
                         dawson, digamma, trigamma, invdigamma, polygamma,
                         airyai, airyaiprime, airybi, airybiprime, besselj0,
                         besselj1, bessely0, bessely1, besselj, bessely, besseli,
                         besselk, hankelh1, hankelh2, polygamma, beta, logbeta

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
                 NaNMath.log10, NaNMath.lgamma, NaNMath.log1p, NaNMath.sqrt]

const diadic = [max, min, hypot, atan, NaNMath.atanh, mod, rem, copysign,
                besselj, bessely, besseli, besselk, hankelh1, hankelh2,
                polygamma, beta, logbeta, NaNMath.pow]
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

for f in vcat(diadic, [+, -, *, \, /, ^])
    @eval promote_symtype(::$(typeof(f)),
                   T::Type{<:Number},
                   S::Type{<:Number}) = promote_type(T, S)
    @eval promote_symtype(::$(typeof(f)),
                   T::Type{<:Rational},
                   S::Type{Integer}) = Rational
    @eval promote_symtype(::$(typeof(f)),
                   T::Type{Integer},
                   S::Type{<:Rational}) = Rational
    @eval promote_symtype(::$(typeof(f)),
                   T::Type{<:Complex{<:Rational}},
                   S::Type{Integer}) = Complex{Rational}
    @eval promote_symtype(::$(typeof(f)),
                   T::Type{Integer},
                   S::Type{<:Complex{<:Rational}}) = Complex{Rational}
end

promote_symtype(::typeof(rem2pi), T::Type{<:Number}, mode) = T

error_f_symbolic(f, T) = error("$f is not defined for T.")

function Base.rem2pi(x::BasicSymbolic{T}, mode::Base.RoundingMode) where {T}
    type = symtype(x)
    type <: Number || error_f_symbolic(rem2pi, type)
    return Term{T}(rem2pi, ArgsT{T}((x, Const{T}(mode))); type)
end

# Specially handle inv and literal pow
function Base.inv(x::BasicSymbolic{T}) where {T}
    type = symtype(x)
    type <: Number || error_f_symbolic(inv, type)
    return Const{T}(x ^ -1)
end
function Base.literal_pow(::typeof(^), x::BasicSymbolic{T}, ::Val{p}) where {T, p}
    type = symtype(x)
    type <: Number || error_f_symbolic(^, type)
    return Const{T}(x ^ p)
end
function promote_symtype(::typeof(Base.literal_pow), _, ::Type{T}, ::Type{Val{S}}) where{T<:Number,S}
    return promote_symtype(^, T, typeof(S))
end

promote_symtype(::Any, T) = promote_type(T, Real)
for f in monadic
    @eval promote_symtype(::$(typeof(f)), T::Type{<:Number}) = promote_type(T, Real)
end

Base.:*(a::AbstractArray, b::BasicSymbolic) = map(x->x*b, a)
Base.:*(a::BasicSymbolic, b::AbstractArray) = map(x->a*x, b)

for f in [identity, one, zero, *, +, -]
    @eval promote_symtype(::$(typeof(f)), T::Type{<:Number}) = T
end

promote_symtype(::typeof(Base.real), T::Type{<:Number}) = Real
function Base.real(s::BasicSymbolic{T}) where {T}
    islike(s, Real) && return s
    @match s begin
        BSImpl.Const(; val) => Const{T}(real(val))
        _ => Term{T}(real, ArgsT{T}((s,)); type = Real)
    end
end
promote_symtype(::typeof(Base.conj), T::Type{<:Number}) = T
function Base.conj(s::BasicSymbolic{T}) where {T}
    islike(s, Real) && return s
    @match s begin
        BSImpl.Const(; val) => Const{T}(conj(val))
        _ => Term{T}(conj, ArgsT{T}((s,)); type = symtype(s))
    end
end
promote_symtype(::typeof(Base.imag), T::Type{<:Number}) = Real
function Base.imag(s::BasicSymbolic{T}) where {T}
    islike(s, Real) && return s
    @match s begin
        BSImpl.Const(; val) => Const{T}(imag(val))
        _ => Term{T}(imag, ArgsT{T}((s,)); type = Real)
    end
end
Base.adjoint(s::BasicSymbolic) = conj(s)


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
        (::$(typeof(f)))(a::BasicSymbolic{<:$Domain}, b::$Domain) = term($f, a, b, type=Bool)
        (::$(typeof(f)))(a::BasicSymbolic{<:$Domain}, b::BasicSymbolic{<:$Domain}) = term($f, a, b, type=Bool)
        (::$(typeof(f)))(a::$Domain, b::BasicSymbolic{<:$Domain}) = term($f, a, b, type=Bool)
    end
end

for f in [!, ~]
    @eval begin
        promote_symtype(::$(typeof(f)), ::Type{<:Bool}) = Bool
        (::$(typeof(f)))(s::BasicSymbolic{Bool}) = Term{Bool}(!, [s])
    end
end


# An ifelse node
function Base.ifelse(_if::BasicSymbolic{Bool}, _then, _else)
    Term{Union{symtype(_then), symtype(_else)}}(ifelse, Any[_if, _then, _else])
end
promote_symtype(::typeof(ifelse), _, ::Type{T}, ::Type{S}) where {T,S} = Union{T, S}

# Array-like operations
Base.size(x::BasicSymbolic{<:Number}) = ()
Base.length(x::BasicSymbolic{<:Number}) = 1
Base.ndims(x::BasicSymbolic{T}) where {T} = Base.ndims(T)
Base.ndims(::Type{<:BasicSymbolic{T}}) where {T} = Base.ndims(T)
Base.broadcastable(x::BasicSymbolic{T}) where {T<:Number} = Ref(x)
