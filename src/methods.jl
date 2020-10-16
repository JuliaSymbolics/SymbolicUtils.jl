const monadic = [deg2rad, rad2deg, transpose, -, conj, asind, log1p, acsch, acos, asec, acosh, acsc, cscd, log, tand, log10, csch, asinh, abs2, cosh, sin, cos, atan, cospi, cbrt, acosd, acoth, inv, acotd, asecd, exp, acot, sqrt, sind, sinpi, asech, log2, tan, exp10, sech, coth, asin, cotd, cosd, sinh, abs, csc, tanh, secd, atand, sec, acscd, cot, exp2, expm1, atanh, real]

const diadic = [+, -, max, min, *, /, \, hypot, atan, mod, rem, ^, copysign]

const previously_declared_for = Set([])

# TODO: it's not possible to dispatch on the symtype! (only problem is Parameter{})
function assert_number(a, b)
    assert_number(a)
    assert_number(b)
end

assert_number(a) = symtype(a) <: Number || error("Can't apply this to not a number")
# TODO: keep domains tighter than this
function number_methods(T, rhs1, rhs2)
    exprs = []

    rhs2 = :($assert_number(a, b); $rhs2)
    rhs1 = :($assert_number(a); $rhs1)

    for f in diadic
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

    for f in monadic
        push!(exprs, :((f::$(typeof(f)))(a::$T)   = $rhs1))
    end
    push!(exprs, :(push!($previously_declared_for, $T)))
    Expr(:block, exprs...)
end

macro number_methods(T, rhs1, rhs2)
    number_methods(T, rhs1, rhs2) |> esc
end

@number_methods(Sym, term(f, a), term(f, a, b))
@number_methods(Term, term(f, a), term(f, a, b))

for f in diadic
    @eval promote_symtype(::$(typeof(f)),
                   T::Type{<:Number},
                   S::Type{<:Number}) = promote_type(T, S)
end
promote_symtype(::typeof(rem2pi), T::Type{<:Number}, mode) = T
Base.rem2pi(x::Symbolic, mode::Base.RoundingMode) = term(rem2pi, x, mode)

for f in monadic
    if f in [real]
        continue
    end
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
    @eval function (::$(typeof(f)))(x::Symbolic, w::Number...)
        term($f, x,w...,
             type=rec_promote_symtype($f, map(symtype, (x,w...))...))
    end
    @eval function (::$(typeof(f)))(x::Number, y::Symbolic, w::Number...)
        term($f, x, y, w...,
             type=rec_promote_symtype($f, map(symtype, (x, y, w...))...))
    end
    @eval function (::$(typeof(f)))(x::Symbolic, y::Symbolic, w::Number...)
        term($f, x, y, w...,
             type=rec_promote_symtype($f, map(symtype, (x, y, w...))...))
    end
end

Base.:*(a::AbstractArray, b::Symbolic{<:Number}) = map(x->x*b, a)
Base.:*(a::Symbolic{<:Number}, b::AbstractArray) = map(x->a*x, b)

for f in [identity, one, zero, *, +]
    @eval promote_symtype(::$(typeof(f)), T::Type{<:Number}) = T
end

promote_symtype(::typeof(Base.real), T::Type{<:Number}) = Real
Base.real(s::Symbolic{<:Real}) = s
Base.real(s::Symbolic{<:Number}) = term(real, s)

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
        (::$(typeof(f)))(a::Symbolic, b::$Domain) = term($f, a, b, type=Bool)
        (::$(typeof(f)))(a::Symbolic, b::Symbolic) = term($f, a, b, type=Bool)
        (::$(typeof(f)))(a::$Domain, b::Symbolic) = term($f, a, b, type=Bool)
    end
end

Base.:!(s::Symbolic{Bool}) = Term{Bool}(!, [s])
Base.:~(s::Symbolic{Bool}) = Term{Bool}(!, [s])


# An ifelse node, ifelse is a built-in unfortunately
#
cond(_if::Bool, _then, _else) = ifelse(_if, _then, _else)
function cond(_if::Symbolic{Bool}, _then, _else)
    Term{Union{symtype(_then), symtype(_else)}}(cond, Any[_if, _then, _else])
end

