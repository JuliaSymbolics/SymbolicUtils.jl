# A total ordering

<ₑ(a::Real,    b::Real) = abs(a) < abs(b)
<ₑ(a::Complex, b::Complex) = (abs(real(a)), abs(imag(a))) < (abs(real(b)), abs(imag(b)))
<ₑ(a::Real,    b::Complex) = true
<ₑ(a::Complex, b::Real) = false

<ₑ(a::Symbolic, b::Number) = false
<ₑ(a::Number,   b::Symbolic) = true

<ₑ(a::Function, b::Function) = nameof(a) <ₑ nameof(b)

<ₑ(a::Type, b::Type) = nameof(a) <ₑ nameof(b)
<ₑ(a::T, b::S) where{T,S} = T<S
<ₑ(a::T, b::T) where{T} = a < b

"""
$(SIGNATURES)

Internal function used for printing symbolic expressions. This function determines
the degrees of symbols within a given expression, implementing a variation on 
degree lexicographic order.
"""
function get_degrees(expr)
    if issym(expr)
        ((Symbol(expr),) => 1,)
    elseif iscall(expr)
        op = operation(expr)
        args = sorted_arguments(expr)
        if op == (^) && (args[2] isa Number || (isconst(args[2]) && args[2].impl.val isa Number))
            return map(get_degrees(args[1])) do (base, pow)
                (base => pow * args[2])
            end
        elseif op == (*)
            return mapreduce(get_degrees,
                             (x,y)->(x...,y...,), args)
        elseif op == (+)
            ds = map(get_degrees, args)
            _, idx = findmax(x->sum(last.(x), init=0), ds)
            return ds[idx]
        elseif op == (getindex)
            return ((Symbol.(args)...,) => 1,)
        else
            return ((Symbol("zzzzzzz", hash(expr)),) => 1,)
        end
    else
        return ()
    end
end

function monomial_lt(degs1, degs2)
    d1 = sum(last, degs1, init=0)
    d2 = sum(last, degs2, init=0)
    d1 != d2 ? d1 < d2 : lexlt(degs1, degs2)
end

function lexlt(degs1, degs2)
    for (a, b) in zip(degs1, degs2)
        if a[1] == b[1] && a[2] != b[2]
            return a[2] > b[2]
        elseif a[1] != b[1]
            return a < b
        end
    end
    return false # they are equal
end

_arglen(a) = iscall(a) ? length(arguments(a)) : 0

function <ₑ(a::Tuple, b::Tuple)
    for (x, y) in zip(a, b)
        if x <ₑ y
            return true
        elseif y <ₑ x
            return false
        end
    end
    return length(a) < length(b)
end

function <ₑ(a::BasicSymbolic, b::BasicSymbolic)
    aisconst = isconst(a)
    if aisconst
        a = a.impl.val
    end
    bisconst = isconst(b)
    if bisconst
        b = b.impl.val
    end
    if aisconst || bisconst
        return a <ₑ b
    end
    da, db = get_degrees(a), get_degrees(b)
    fw = monomial_lt(da, db)
    bw = monomial_lt(db, da)
    if fw === bw && !isequal(a, b)
        if _arglen(a) == _arglen(b)
            return (operation(a), arguments(a)...) <ₑ (operation(b), arguments(b)...)
        else
            return _arglen(a) < _arglen(b)
        end
    else
        return fw
    end
end
