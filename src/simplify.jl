# A total ordering
<ₑ(a::Real,    b::Real) = a < b
<ₑ(a::Complex, b::Complex) = (real(a), imag(a)) < (real(b), imag(b))
<ₑ(a::Real,    b::Complex) = true
<ₑ(a::Complex, b::Real) = false

<ₑ(a::Symbolic, b::Number) = true
<ₑ(a::Number,   b::Symbolic) = false

<ₑ(a::Variable, b::Symbolic) = true
<ₑ(a::Variable, b::Variable) = a.name <ₑ b.name

function <ₑ(a::Term, b::Term)
    na = nameof(a)
    nb = nameof(b)
    if na !== nb
        return na < nb
    else
        aa, ab = arguments(a), arguments(b)
        if length(aa) !== length(ab)
            return aa < ab
        else
            return any(<ₑ, aa, ab) || false
        end
    end
end
isnumber(x) = x isa Number

const plus_and_scalar_mul = let
    [
     # Associativity of * (moves numbers to the end)
     @rule(*(~~y) => *(flatten_args(*, 1, ~y)...)),

     # Associativity of + (also moves numbers to the back)
     @rule(+(~~x) => +(flatten_args(+, 0, ~x)...)),

     # Commutativity of +
     @rule(+(~~x) => sort_args(~x)),

     # addition of the same term
     @rule(+(~~a, *(~~x, ~α::isnumber), *(~~x, ~β::isnumber), ~~b) => +((~~a)..., *(*(~α, ~β), (~x)...), (~b)...))
    ]
end

function move_numbers_to_end(args)
    if !any(isnumber, args)
        return nothing
    else
        flatten_args(*, 1, args)
    end
end

# Numbers to the back
function flatten_args(⋆, init, args)
    # flatten nested +
    flattened_numeric  = Number[]
    flattened_symbolic = Any[]

    for t in args
        if t isa Term && operation(t) === (⋆)
            for a in arguments(t)
                if t isa Number
                    push!(flattened_numeric, a)
                else
                    push!(flattened_symbolic, a)
                end
            end
        end
    end
    s = reduce(⋆, flattened_numeric, init=init)
    s == init ? flattened_symbolic : push!(flattened_symbolic, s)
end

function sort_args(args)
    if length(args) < 2
        return args
    elseif length(args) == 2
        x, y = args
        return x <ₑ y ? nothing : (y,x)
    end

    if issorted(args, lt=<ₑ)
        return nothing
    end
    sort!(args, lt=<ₑ)
end
