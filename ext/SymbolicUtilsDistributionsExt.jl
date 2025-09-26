module SymbolicUtilsDistributionsExt

using SymbolicUtils
using SymbolicUtils: BasicSymbolic, BSImpl, ArgsT, Const, ShapeT, ShapeVecT,
                     promote_symtype, promote_shape, shape, symtype
using Distributions

for f in [pdf, logpdf, cdf, logcdf, quantile]
    @eval function SymbolicUtils.promote_symtype(::$(typeof(f)), ::Type{T},
                                   ::Type{S}) where {T <: Distributions.Distribution,
                                                     S <: Number}
        S
    end
    @eval function SymbolicUtils.promote_symtype(::$(typeof(f)), ::Type{T},
                                   ::Type{S}) where {T <: Distributions.Distribution,
                                                     eS <: Number, S <: AbstractArray{eS}}
        S
    end
    @eval function SymbolicUtils.promote_symtype(::$(typeof(f)), ::Type{T},
                                   ::Type{S}) where {T <: Distributions.Distribution, S}
        error("Distributions can only be sampled with numbers or arrays of numbers.")
    end
    @eval function SymbolicUtils.promote_symtype(::$(typeof(f)), ::Type{T},
                                   ::Type{S}) where {T, S}
        error("Distributions.jl sample functions require a distribution as the first argument.")
    end
    @eval function SymbolicUtils.promote_shape(::$(typeof(f)), sh::ShapeT)
        @nospecialize sh
        return sh
    end
    @eval function (::$(typeof(f)))(dist::Distributions.Distribution, x::BasicSymbolic{T}) where {T}
        return BSImpl.Term{T}($f, ArgsT{T}((Const{T}(dist), x)); shape = shape(x), type = symtype(x))
    end
    @eval function (::$(typeof(f)))(dist::BasicSymbolic{T}, x::BasicSymbolic{T}) where {T}
        return BSImpl.Term{T}($f, ArgsT{T}((dist, x)); shape = shape(x), type = symtype(x))
    end
    @eval function (::$(typeof(f)))(dist::BasicSymbolic{T}, x) where {T}
        return BSImpl.Term{T}($f, ArgsT{T}((dist, Const{T}(x))); shape = shape(x), type = symtype(x))
    end
end

for f in [Distributions.Uniform, Distributions.Normal]
    @eval function SymbolicUtils.promote_symtype(::Type{$f}, ::Type{T}, ::Type{S}) where {T <: Real, S <: Real}
        $f{promote_type(T, S)}
    end
    @eval function SymbolicUtils.promote_shape(::Type{$f}, sha::ShapeT, shb::ShapeT)
        @nospecialize sha shb
        @assert sha isa ShapeVecT && isempty(sha) "Distribution requires scalar inputs"
        @assert shb isa ShapeVecT && isempty(shb) "Distribution requires scalar inputs"
        return ShapeVecT()
    end
    for (T1, T2) in Iterators.product(Iterators.repeated([Real, :($BasicSymbolic{T})], 2)...)
        if T1 == T2 == Real
            continue
        end
        @eval function (::Type{$f})(a::$T1, b::$T2) where {T}
            type = promote_symtype($f, symtype(a), symtype(b))
            sh = promote_shape($f, shape(a), shape(b))
            BSImpl.Term{T}($f, ArgsT{T}((Const{T}(a), Const{T}(b))); type, shape = sh)
        end
    end
end

end
