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

promote_symtype(::typeof(rem2pi), T::Type{<:Number}, mode) = T

error_f_symbolic(f, T) = error("$f is not defined for T.")

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

# Specially handle inv and literal pow
function Base.inv(x::BasicSymbolic{T}) where {T}
    sh = shape(x)
    type = promote_symtype(inv, symtype(x))
    if _is_array_shape(sh)
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
    @eval promote_symtype(::$(typeof(f)), T::Type{<:Number}) = promote_type(T, Real)
end

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
function Base.ifelse(_if::BasicSymbolic{T}, _then::BasicSymbolic{T}, _else::BasicSymbolic{T}) where {T}
    if symtype(_if) !== Bool
        throw(MethodError(!, (_if, _then, _else)))
    end
    type = Union{symtype(_then), symtype(_else)}
    Term{T}(ifelse, ArgsT{T}((_if, _then, _else)); type)
end
promote_symtype(::typeof(ifelse), _, ::Type{T}, ::Type{S}) where {T,S} = Union{T, S}

# Array-like operations
function _size_from_shape(shape::ShapeT)
    @nospecialize shape
    if shape isa Unknown
        return shape
    else
        return Tuple(map(length, shape))
    end
end
Base.size(x::BasicSymbolic) = _size_from_shape(shape(x))
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
Base.broadcastable(x::BasicSymbolic) = _is_array_shape(shape(x)) ? x : Ref(x)
function Base.eachindex(x::BasicSymbolic)
    sh = shape(x)
    if sh isa Unknown
        throw(ArgumentError("Indices of variable $x with unknown shape $sh are not defined."))
    end
    CartesianIndices(Tuple(sh))
end
function Base.collect(x::BasicSymbolic)
    [x[i] for i in eachindex(x)]
end
struct SymBroadcast{T <: SymVariant} <: Broadcast.BroadcastStyle end
Broadcast.BroadcastStyle(::Type{BasicSymbolic{T}}) where {T} = SymBroadcast{T}()
Broadcast.result_style(::SymBroadcast{T}) where {T} = SymBroadcast{T}()
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
        is_arr = _is_array_shape(sh)
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
                push!(getindex_args,  length(bc.axes[i]) == 1 ? Const{T}(1) : subscripts[i])
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
