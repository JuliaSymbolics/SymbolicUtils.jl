const monadic = [deg2rad, rad2deg, transpose, -, conj, asind, log1p, acsch, acos, asec, acosh, acsc, cscd, log, tand, log10, csch, asinh, abs2, cosh, sin, cos, atan, cospi, cbrt, acosd, acoth, inv, acotd, asecd, exp, acot, sqrt, sind, sinpi, asech, log2, tan, exp10, sech, coth, asin, cotd, cosd, sinh, abs, csc, tanh, secd, atand, sec, acscd, cot, exp2, expm1, atanh]

const diadic = [+, -, max, min, *, /, \, hypot, atan, mod, rem, ^]

# TODO: keep domains tighter than this
for f in diadic
    @eval promote_symtype(::$(typeof(f)),
                   T::Type{<:Number},
                   S::Type{<:Number}) = promote_type(T, S)

    for T in [Sym, Term]
        for S in [Sym, Term]
            @eval (::$(typeof(f)))(a::$T, b::$S) = term($f, a, b)
        end
        @eval begin
            (::$(typeof(f)))(a::$T, b::Real)   = term($f, a, b)
            (::$(typeof(f)))(a::Real, b::$T)   = term($f, a, b)
            (::$(typeof(f)))(a::$T, b::Number) = term($f, a, b)
            (::$(typeof(f)))(a::Number, b::$T) = term($f, a, b)
        end
    end
end

promote_symtype(::typeof(rem2pi), T::Type{<:Number}, mode) = T
Base.rem2pi(x::Symbolic, mode::Base.RoundingMode) = term(rem2pi, x, mode)

for f in monadic
    @eval promote_symtype(::$(typeof(f)), T::Type{<:Number}) = Number
    @eval (::$(typeof(f)))(a::Symbolic)   = term($f, a)
end

rec_promote_symtype(f) = promote_symtype(f)
rec_promote_symtype(f, x) = promote_symtype(f, x)
rec_promote_symtype(f, x,y) = promote_symtype(f, x,y)
rec_promote_symtype(f, x,y,z...) = rec_promote_symtype(f, promote_symtype(f, x,y), z...)

# Variadic methods
for f in [+, *]

    @eval (::$(typeof(f)))(x::Symbolic) = x

    # single arg
    @eval function (::$(typeof(f)))(x::Symbolic, w...)
        term($f, x,w...,
             type=rec_promote_symtype($f, map(symtype, (x,w...))...))
    end
    @eval function (::$(typeof(f)))(x, y::Symbolic, w...)
        term($f, x, y, w...,
             type=rec_promote_symtype($f, map(symtype, (x, y, w...))...))
    end
    @eval function (::$(typeof(f)))(x::Symbolic, y::Symbolic, w...)
        term($f, x, y, w...,
             type=rec_promote_symtype($f, map(symtype, (x, y, w...))...))
    end
end

for f in [identity, one, *, +]
    @eval promote_symtype(::$(typeof(f)), T::Type{<:Number}) = T
end

## Booleans

# binary ops that return Bool
for (f, Domain) in [(==) => Number, (!=) => Number,
                    (<=) => Real,   (>=) => Real,
                    (< ) => Real,   (> ) => Real,
                    (& ) => Bool,   (| ) => Bool,
                    xor => Bool]
    @eval begin
        promote_symtype(::$(typeof(f)), ::Type{<:$Domain}, ::Type{<:$Domain}) = Bool
        (::$(typeof(f)))(a::Symbolic{<:$Domain}, b::$Domain) = term($f, a, b, type=Bool)
        (::$(typeof(f)))(a::Symbolic{<:$Domain}, b::Symbolic{<:$Domain}) = term($f, a, b, type=Bool)
        (::$(typeof(f)))(a::$Domain, b::Symbolic{<:$Domain}) = term($f, a, b, type=Bool)
    end
end

Base.:!(s::Symbolic{Bool}) = Term{Bool}(!, [s])
Base.:~(s::Symbolic{Bool}) = Term{Bool}(!, [s])

# An ifelse node, ifelse is a built-in unfortunately
function cond(_if, _then, _else)
    Term{Union{symtype(_then), symtype(_else)}}(cond, Any[_if, _then, _else])
end
