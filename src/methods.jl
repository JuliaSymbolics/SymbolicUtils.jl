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
                 airybiprime, besselj0, besselj1, bessely0, bessely1]

const diadic = [max, min, hypot, atan, mod, rem, copysign,
                besselj, bessely, besseli, besselk, hankelh1, hankelh2,
                polygamma, beta, logbeta]
const previously_declared_for = Set([])

# TODO: it's not possible to dispatch on the symtype! (only problem is Parameter{})

assert_like(f, T) = nothing
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
    skips = Meta.isexpr(options, [:vcat, :hcat, :vect]) ? Set(options.args) : []
    basic_monadic = [-, +]
    basic_diadic = [+, -, *, /, //, \, ^]

    rhs2 = :($assert_like(f, Number, a, b); $rhs2)
    rhs1 = :($assert_like(f, Number, a); $rhs1)

    for f in (skip_basics ? diadic : vcat(basic_diadic, diadic))
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
    end

    for f in (skip_basics ? monadic : vcat(basic_monadic, monadic))
        nameof(f) in skips && continue
        push!(exprs, :((f::$(typeof(f)))(a::$T)   = $rhs1))
    end
    push!(exprs, :(push!($previously_declared_for, $T)))
    Expr(:block, exprs...)
end

macro number_methods(T, rhs1, rhs2, options=nothing)
    number_methods(T, rhs1, rhs2, options) |> esc
end

@number_methods(Sym, term(f, a), term(f, a, b), skipbasics)
@number_methods(Term, term(f, a), term(f, a, b), skipbasics)
@number_methods(Add, term(f, a), term(f, a, b), skipbasics)
@number_methods(Mul, term(f, a), term(f, a, b), skipbasics)
@number_methods(Pow, term(f, a), term(f, a, b), skipbasics)
@number_methods(Div, term(f, a), term(f, a, b), skipbasics)

for f in diadic
    @eval promote_symtype(::$(typeof(f)),
                   T::Type{<:Number},
                   S::Type{<:Number}) = promote_type(T, S)
end

for f in [+, -, *, \, /, ^]
    @eval promote_symtype(::$(typeof(f)),
                   T::Type{<:Number},
                   S::Type{<:Number}) = promote_type(T, S)
end

promote_symtype(::typeof(rem2pi), T::Type{<:Number}, mode) = T
Base.rem2pi(x::Symbolic{<:Number}, mode::Base.RoundingMode) = term(rem2pi, x, mode)

for f in monadic
    @eval promote_symtype(::$(typeof(f)), T::Type{<:Number}) = promote_type(T, Real)
    @eval (::$(typeof(f)))(a::Symbolic{<:Number})   = term($f, a)
end

Base.:*(a::AbstractArray, b::Symbolic{<:Number}) = map(x->x*b, a)
Base.:*(a::Symbolic{<:Number}, b::AbstractArray) = map(x->a*x, b)

for f in [identity, one, zero, *, +, -]
    @eval promote_symtype(::$(typeof(f)), T::Type{<:Number}) = T
end

promote_symtype(::typeof(Base.real), T::Type{<:Number}) = Real
Base.real(s::Symbolic{<:Number}) = islike(s, Real) ? s : term(real, s)
promote_symtype(::typeof(Base.conj), T::Type{<:Number}) = T
Base.conj(s::Symbolic{<:Number}) = islike(s, Real) ? s : term(conj, s)
promote_symtype(::typeof(Base.imag), T::Type{<:Number}) = Real
Base.imag(s::Symbolic{<:Number}) = islike(s, Real) ? zero(symtype(s)) : term(imag, s)

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
        (::$(typeof(f)))(a::Symbolic{<:$Domain}, b::$Domain) = term($f, a, b, type=Bool)
        (::$(typeof(f)))(a::Symbolic{<:$Domain}, b::Symbolic{<:$Domain}) = term($f, a, b, type=Bool)
        (::$(typeof(f)))(a::$Domain, b::Symbolic{<:$Domain}) = term($f, a, b, type=Bool)
    end
end

for f in [!, ~]
    @eval begin
        promote_symtype(::$(typeof(f)), ::Type{<:Bool}) = Bool
        (::$(typeof(f)))(s::Symbolic{Bool}) = Term{Bool}(!, [s])
    end
end


# An ifelse node, ifelse is a built-in unfortunately
# So this uses IfElse.jl's ifelse that we imported
function ifelse(_if::Symbolic{Bool}, _then, _else)
    Term{Union{symtype(_then), symtype(_else)}}(ifelse, Any[_if, _then, _else])
end
promote_symtype(::typeof(ifelse), _, ::Type{T}, ::Type{S}) where {T,S} = Union{T, S}

# Specially handle inv and literal pow
Base.inv(x::Symbolic{<:Number}) = Base.:^(x, -1)
Base.literal_pow(::typeof(^), x::Symbolic{<:Number}, ::Val{p}) where {p} = Base.:^(x, p)

# Array-like operations
Base.size(x::Symbolic{<:Number}) = ()
Base.length(x::Symbolic{<:Number}) = 1
Base.ndims(x::Symbolic{T}) where {T} = Base.ndims(T)
Base.ndims(::Type{<:Symbolic{T}}) where {T} = Base.ndims(T)
Base.broadcastable(x::Symbolic{T}) where {T} = Ref(x)
