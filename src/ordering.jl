# A total ordering

<ₑ(a::Real,    b::Real) = abs(a) < abs(b)
<ₑ(a::Complex, b::Complex) = (abs(real(a)), abs(imag(a))) < (abs(real(b)), abs(imag(b)))
<ₑ(a::Real,    b::Complex) = true
<ₑ(a::Complex, b::Real) = false

<ₑ(a::Symbolic, b::Number) = false
<ₑ(a::Number,   b::Symbolic) = true

arglength(a) = length(arguments(a))
function <ₑ(a, b)
    if isterm(a) && (b isa Symbolic && !isterm(b))
        return false
    elseif isterm(b) && (a isa Symbolic && !isterm(a))
        return true
    elseif (isadd(a) || ismul(a)) && (isadd(b) || ismul(b))
        return cmp_mul_adds(a, b)
    elseif issym(a) && issym(b)
        nameof(a) < nameof(b)
    elseif !istree(a) && !istree(b)
        T = typeof(a)
        S = typeof(b)
        return T===S ? (T <: Number ? isless(a, b) : hash(a) < hash(b)) : nameof(T) < nameof(S)
    elseif istree(b) && !istree(a)
        return true
    elseif istree(a) && istree(b)
        return cmp_term_term(a,b)
    else
        return !(b <ₑ a)
    end
end

function cmp_mul_adds(a, b)
    (isadd(a) && ismul(b)) && return true
    (ismul(a) && isadd(b)) && return false
    a_args = unsorted_arguments(a)
    b_args = unsorted_arguments(b)
    length(a_args) < length(b_args) && return true
    length(a_args) > length(b_args) && return false
    a_args = arguments(a)
    b_args = arguments(b)
    for (x, y) in zip(a_args, b_args)
        x <ₑ y && return true
    end
    return false
end

function <ₑ(a::Symbol, b::Symbol)
    # Enforce the order [+,-,\,/,^,*]
    if b === :*
        a in (:^, :/, :\, :-, :+)
    elseif b === :^
        a in (:/, :\, :-, :+) && return true
    elseif b === :/
        a in (:\, :-, :+) && return true
    elseif b === :\
        a in (:-, :+) && return true
    elseif b === :-
        a === :+ && return true
    elseif a in (:*, :^, :/, :-, :+)
        false
    else
        a < b
    end
end

<ₑ(a::Function, b::Function) = nameof(a) <ₑ nameof(b)

<ₑ(a::Type, b::Type) = nameof(a) <ₑ nameof(b)

function cmp_term_term(a, b)
    la = arglength(a)
    lb = arglength(b)

    if la == 0 && lb == 0
        return operation(a) <ₑ operation(b)
    elseif la === 0
        return operation(a) <ₑ b
    elseif lb === 0
        return a <ₑ operation(b)
    end

    na = operation(a)
    nb = operation(b)

    if 0 < arglength(a) <= 2 && 0 < arglength(b) <= 2
        # e.g. a < sin(a) < b ^ 2 < b
        @goto compare_args
    end

    if na !== nb
        return na <ₑ nb
    elseif arglength(a) != arglength(b)
        return arglength(a) < arglength(b)
    else
        @label compare_args
        aa, ab = arguments(a), arguments(b)
        if length(aa) !== length(ab)
            return length(aa) < length(ab)
        else
            terms = zip(Iterators.filter(!is_literal_number, aa), Iterators.filter(!is_literal_number, ab))

            for (x,y) in terms
                if x <ₑ y
                    return true
                elseif y <ₑ x
                    return false
                end
            end

            # compare the numbers
            nums = zip(Iterators.filter(is_literal_number, aa),
                       Iterators.filter(is_literal_number, ab))

            for (x,y) in nums
                if x <ₑ y
                    return true
                elseif y <ₑ x
                    return false
                end
            end

        end
        return na <ₑ nb # all args are equal, compare the name
    end
end
