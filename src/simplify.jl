##### Numeric simplification
### Predicates

isnumber(x) = x isa Number

_iszero(t) = false
_iszero(x::Number) = iszero(x)
_isone(t) = false
_isone(x::Number) = isone(x)

# A total ordering
<ₑ(a::Real,    b::Real) = a < b
<ₑ(a::Complex, b::Complex) = (real(a), imag(a)) < (real(b), imag(b))
<ₑ(a::Real,    b::Complex) = true
<ₑ(a::Complex, b::Real) = false

<ₑ(a::Symbolic, b::Number) = false
<ₑ(a::Number,   b::Symbolic) = true

<ₑ(a::Variable, b::Symbolic) = false
<ₑ(a::Symbolic, b::Variable) = true
<ₑ(a::Variable, b::Variable) = a.name < b.name
<ₑ(a::T, b::S) where {T, S} = T===S ? isless(a, b) : nameof(T) < nameof(S)

function <ₑ(a::Term, b::Term)
    na = nameof(operation(a))
    nb = nameof(operation(b))
    if na !== nb
        return na < nb
    else
        aa, ab = arguments(a), arguments(b)
        if length(aa) !== length(ab)
            return length(aa) < length(ab)
        else
            terms = zip(Iterators.filter(!isnumber, aa), Iterators.filter(!isnumber, ab))

            for (x,y) in terms
                if x <ₑ y
                    return true
                elseif y <ₑ x
                    return false
                end
            end

            # compare the numbers
            nums = zip(Iterators.filter(isnumber, aa),
                       Iterators.filter(isnumber, ab))
            return any(a <ₑ b for (a, b) in nums)
        end
    end
end

issortedₑ(args) = issorted(args, lt=<ₑ)
issortedₑ(args::Tuple) = issorted([args...], lt=<ₑ)
issortedₑ((a,b,)::Tuple{Any,Any}) = isequal(a, b) || a <ₑ b
issortedₑ(a::Tuple{Any}) = true

# are there nested ⋆ terms?
function isnotflat(⋆)
    function (args)
        for t in args
            if t isa Term && operation(t) === (⋆)
                return true
            end
        end
        return false
    end
end

### Simplification rules

PLUS_AND_SCALAR_MUL = let
    [
     #@rule(*(~~x, *(~~y), ~~z) => *((~~x)..., (~~y)..., (~~z)...)),
     # Flatten *
     @rule(*(~~x::isnotflat(*)) => flatten_term(*, ~~x)),
     # Commute *
     @rule(*(~~x::!(issortedₑ)) => sort_args(*, ~~x)),

     @rule(~x - ~y => ~x + (-1 * ~y)),
     #@rule(+(~~x, +(~~y), ~~z) => +((~~x)..., (~~y)..., (~~z)...)),
     # Flatten +
     @rule(+(~~x::isnotflat(+)) => flatten_term(+, ~~x)),
     # Commute +
     @rule(+(~~x::!(issortedₑ)) => sort_args(+, ~~x)),

     # Group terms
     @rule(+(~~a, ~x, ~x, ~~b) => +((~~a)..., 2(~x), (~~b)...)),
     @rule(*(~~x, ~a::isnumber, ~b::isnumber) => *((~~x)..., ~a * ~b)),
     @rule(+(~~x, ~a::isnumber, ~b::isnumber) => +((~~x)..., ~a + ~b)),
     @rule(+(~~a, *(~~x), *(~~x, ~β::isnumber), ~~b) => +((~~a)..., *(1 + ~β, (~x)...), (~b)...)),
     @rule(+(~~a, *(~~x, ~α::isnumber), *(~~x, ~β::isnumber), ~~b) => +((~~a)..., *(~α + ~β, (~x)...), (~b)...)),
     @rule(*(~~x, ~z::_iszero) => ~z),

     # remove the idenitities
     @rule(*(~~x::(!isempty), ~z::_isone) => *((~~x)...)),
     @rule(*(~x) => ~x),
     @rule(+(~~x::(!isempty), ~z::_iszero) => +((~~x)...)),
     @rule(+(~x) => ~x),
    ]
end

simplifynum(x) = rewriter(PLUS_AND_SCALAR_MUL)(x)

# Numbers to the back
function flatten_term(⋆, args)
    # flatten nested ⋆
    flattened_args = []
    for t in args
        if t isa Term && operation(t) === (⋆)
            append!(flattened_args, arguments(t))
        else
            push!(flattened_args, t)
        end
    end
    Term(⋆, Number, flattened_args)
end

function sort_args(f, args)
    if length(args) < 2
        return Term(f, Number, args)
    elseif length(args) == 2
        x, y = args
        return Term(f, Number, x <ₑ y ? [x,y] : [y,x])
    end

    args = args isa Tuple ? [args...] : args
    Term(f, Number, sort(args, lt=<ₑ))
end
