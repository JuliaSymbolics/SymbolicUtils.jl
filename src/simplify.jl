##### Numeric simplification
### Predicates

multiple_of(x, tol=1e-10) = y -> (y isa Number) && abs(y % x) < 1e-10

isnumber(x) = x isa Number

_iszero(t) = false
_iszero(x::Number) = iszero(x)
_isone(t) = false
_isone(x::Number) = isone(x)

# A total ordering
<ₑ(a::Real,    b::Real) = abs(a) < abs(b)
<ₑ(a::Complex, b::Complex) = (abs(real(a)), abs(imag(a))) < (abs(real(b)), abs(imag(b)))
<ₑ(a::Real,    b::Complex) = true
<ₑ(a::Complex, b::Real) = false

<ₑ(a::Symbolic, b::Number) = false
<ₑ(a::Number,   b::Symbolic) = true

arglength(a) = length(arguments(a))
function <ₑ(a::Variable, b::Term)
    args = arguments(b)
    if length(args) === 2
        n1, n2 = !isnumber(args[1]) , !isnumber(args[2])
        if n1 && n2
            # both subterms are terms, so it's definitely firster
            return true
        elseif n1
            if a <ₑ args[1]
                return true
            else
                return false
            end
        elseif n2
            if a <ₑ args[2]
                return true
            else
                return false
            end
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

<ₑ(a::Symbolic, b::Variable) = !(b <ₑ a)

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

<ₑ(a::Variable, b::Variable) = a.name < b.name
<ₑ(a::T, b::S) where {T, S} = T===S ? isless(a, b) : nameof(T) < nameof(S)

function <ₑ(a::Term, b::Term)
    if 0 < arglength(a) <= 2 && 0 < arglength(b) <= 2
        # e.g. a < sin(a) < b ^ 2 < b
        @goto compare_args
    end
    na = nameof(operation(a))
    nb = nameof(operation(b))
    if na !== nb
        return na < nb
    elseif arglength(a) != arglength(b)
        return arglength(a) < arglength(b)
    else
        @label compare_args
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
        return na <ₑ nb
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

function hasrepeats(x)
    length(x) <= 1 && return false
    for i=1:length(x)-1
        if isequal(x[i], x[i+1])
            return true
        end
    end
    return false
end

function merge_repeats(merge, xs)
    length(xs) <= 1 && return false
    merged = Any[]
    i=1

    while i<=length(xs)
        l = 1
        for j=i+1:length(xs)
            if isequal(xs[i], xs[j])
                l += 1
            else
                break
            end
        end
        if l > 1
            push!(merged, merge(xs[i], l))
        else
            push!(merged, xs[i])
        end
        i+=l
    end
    return merged
end

### Simplification rules

simplify(x, rules=SIMPLIFY_RULES) = RuleSet(rules)(to_symbolic(x))

pow(x,y) = y==0 ? 1 : y<0 ? inv(x)^(-y) : x^y
pow(x::Symbolic,y) = y==0 ? 1 : Base.:^(x,y)

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
    Term(⋆, flattened_args)
end

function sort_args(f, args)
    if length(args) < 2
        return Term(f, args)
    elseif length(args) == 2
        x, y = args
        return Term(f, x <ₑ y ? [x,y] : [y,x])
    end
    args = args isa Tuple ? [args...] : args
    Term(f, sort(args, lt=<ₑ))
end
