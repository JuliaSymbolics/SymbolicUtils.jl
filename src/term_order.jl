# A total ordering

# c
<ₑ(a::Real,    b::Real) = a < b
<ₑ(a::Complex, b::Complex) = (real(a), imag(a)) < (real(b), imag(b))
<ₑ(a::Real,    b::Complex) = true
<ₑ(a::Complex, b::Real) = false

# c <ₑ x
<ₑ(a::Symbolic, b::Number) = false
<ₑ(a::Number,   b::Symbolic) = true

# fails: (x*exp(x)*(x+1)^8*(x+y))*y^3

# x <ₑ f(x)
function <ₑ(a::Sym, b::Term)
    args = arguments(b)
    if length(args) === 2
        n1, n2 = !isnumber(args[1]) , !isnumber(args[2])
        if n1 && n2
            # e.g. (x + y) goes to the right of x
            return true
        elseif n1
            return  a <ₑ args[1] || isequal(a, args[1])
        elseif n2
            return a <ₑ args[2] || isequal(a, args[2])
        else
            # both arguments are not numbers
            # This case when a <ₑ Term(^, [1,-1])
            # so this term should go to the left.
            return false
        end
    elseif length(args) === 1
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
end

<ₑ(a::Symbolic, b::Sym) = !(b <ₑ a)

function <ₑ(a::Symbol, b::Symbol)
    # Enforce the order [+,-,\,/,^,*]
    if b === :^
        return !(a == :^)
    end
    a < b
end

<ₑ(a::Sym, b::Sym) = a.name < b.name
<ₑ(a::T, b::S) where {T, S} = T===S ? isless(a, b) : nameof(T) < nameof(S)

# return number of symbols in a term and the highest symbol
function short_cmpargs(aa, bb, na, nb)
    # <= 2 arguments
    if length(aa) == 1 && length(bb) == 1
        aa[1] <ₑ bb[1] && return true
    elseif length(aa) == 1 && length(bb) == 2
        # check if the largest term in b is bigger than a
        (aa[1] <ₑ bb[1] || aa[1] <ₑ bb[2]) && return true
    elseif length(aa) == 2 && length(bb) == 1
        # check if the largest term in a is smaller than b
        (aa[1] <ₑ bb[1] && aa[2] <ₑ bb[1]) && return true
        return false
    elseif length(aa) == 2 && length(bb) == 2
        if na == nb && na == :^
            # not all arguments are created equal
            aa[1] <ₑ bb[1] && return true
            !(bb[1] <ₑ aa[1]) && return aa[2] <ₑ bb[2] # equiv base
            return false
        elseif aa[1] <ₑ aa[2]
            aa[2] <ₑ bb[2] && return true
            na == nb && !(bb[2] <ₑ aa[2]) && return aa[1] <ₑ bb[1]
        elseif aa[2] <ₑ aa[1]
            aa[1] <ₑ bb[2] && return true
            na == nb && !(bb[2] <ₑ aa[1]) && return aa[1] <ₑ bb[1]
        end
    end
    return na <ₑ nb
end

function long_cmpargs(aa, bb, na, nb)
    # compare non-numbers
    terms = zip(Iterators.filter(!isnumber, aa),
                Iterators.filter(!isnumber, bb))

    for (x,y) in terms
        if x <ₑ y
            return true
        elseif y <ₑ x
            return false
        end
    end

    # compare the numbers
    nums = zip(Iterators.filter(isnumber, aa),
               Iterators.filter(isnumber, bb))

    for (x,y) in nums
        if x <ₑ y
            return true
        elseif y <ₑ x
            return false
        end
    end

    return na <ₑ nb
end

equiv(a, b) = !(a <ₑ b) && !(b <ₑ a)
equiv(x) = y->equiv(x, y)

function <ₑ(a::Term, b::Term)
    aa, bb = arguments(a), arguments(b)

    if length(aa) === 0
        return operation(a) <ₑ b
    elseif length(bb) === 0
        return a <ₑ operation(b)
    end

    na = nameof(operation(a))
    nb = nameof(operation(b))

    if length(aa) <= 2 && length(bb) <= 2
        if na !== nb
            if nb == :^
                #3x^2 < x^3
                return all(x -> isnumber(x) || x <ₑ b, aa)
            elseif na == :^
                return !all(x -> isnumber(x) || x <ₑ a, bb)
            elseif nb == :*
                # sin(x) < sin(x)*x
                return any(x -> !isnumber(x) && x <ₑ b, aa)
            elseif na == :*
                return !any(x -> !isnumber(x) && x <ₑ a, bb)
            end
        end
        return short_cmpargs(aa, bb, na, nb)
    else
        # order terms longer than 2 args by length or name for now -- it
        # should give priority to the term with the largest complexity
        length(aa) != length(bb) && return length(aa) < length(bb)
        na != nb && return na <ₑ nb
        return long_cmpargs(aa, bb, na, nb)
    end
end
