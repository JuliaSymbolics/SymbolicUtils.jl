# A total ordering

<ₑ(a::Real,    b::Real) = abs(a) < abs(b)
<ₑ(a::Complex, b::Complex) = (abs(real(a)), abs(imag(a))) < (abs(real(b)), abs(imag(b)))
<ₑ(a::Real,    b::Complex) = true
<ₑ(a::Complex, b::Real) = false

<ₑ(a::Symbolic, b::Number) = false
<ₑ(a::Number,   b::Symbolic) = true

arglength(a) = length(arguments(a))
function <ₑ(a, b)
    if !istree(a) && !istree(b)
        T = typeof(a)
        S = typeof(b)
        T===S ? isless(a, b) : nameof(T) < nameof(S)
    elseif istree(b) && !istree(a)
        args = arguments(b)
        if length(args) === 2
            n1, n2 = !is_literal_number(args[1]) , !is_literal_number(args[2])
            if n1 && n2
                # both subterms are terms, so it's definitely firster
                return true
            elseif n1
                return isequal(a, args[1]) || a <ₑ args[1]
            elseif n2
                return isequal(a, args[2]) || a <ₑ args[2]
            else
                # both arguments are not numbers
                # This case when a <ₑ Term(^, [1,-1])
                # so this term should go to the left.
                return false
            end
        elseif length(args) === 1
            if operation(b) isa Sym
                return true
            end
            # make sure a < sin(a) < b^2 < b
            if isequal(a, args[1])
                return true # e.g sin(a)*a should become a*sin(a)
            else
                return a<ₑargs[1]
            end
        else
            # variables to the right
            return false
        end
    elseif istree(a) && istree(b)
        cmp_term_term(a,b)
    else
        !(b <ₑ a)
    end
end

<ₑ(a::Symbolic, b::Sym) = !(b <ₑ a)

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

<ₑ(a::Sym, b::Sym) = a.name < b.name

function cmp_term_term(a, b)
    la = arglength(a)
    lb = arglength(b)

    if la == 0 && lb == 0
        return nameof(operation(a)) <ₑ nameof(operation(b))
    elseif la === 0
        return operation(a) <ₑ b
    elseif lb === 0
        return a <ₑ operation(b)
    end

    na = nameof(operation(a))
    nb = nameof(operation(b))

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

