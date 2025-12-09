# A total ordering

<ₑ(a::Real,    b::Real) = abs(a) < abs(b)
<ₑ(a::Complex, b::Complex) = (abs(real(a)), abs(imag(a))) < (abs(real(b)), abs(imag(b)))
<ₑ(a::Real,    b::Complex) = true
<ₑ(a::Complex, b::Real) = false

<ₑ(a::BasicSymbolic, b::Number) = false
<ₑ(a::Number, b::BasicSymbolic) = true

<ₑ(a::Function, b::Function) = nameof(a) <ₑ nameof(b)

<ₑ(a::Type, b::Type) = nameof(a) <ₑ nameof(b)
<ₑ(a::T, b::S) where{T,S} = T<S
<ₑ(a::T, b::T) where{T} = a < b

"""
$(SIGNATURES)

Get the degrees of symbols within a given expression.

This internal function is used to define the order of terms in a symbolic expression,
which is a variation on degree lexicographic order. It is used for printing and
by [`sorted_arguments`](@ref).

Returns a tuple of degree and lexicographically sorted *multiplier* ⇒ *power* pairs,
where the *multiplier* is a tuple of the symbol optionally followed by its indices.
For a sum expression, returns the `get_degrees()` result for term with the highest degree.

See also `monomial_lt` and `lexlt`.
"""
function get_degrees(expr::BasicSymbolic{T}) where {T}
    if T === SymReal
        return _get_degrees_1(expr)
    elseif T === SafeReal
        return _get_degrees_2(expr)
    elseif T === TreeReal
        return _get_degrees_3(expr)
    end
    _unreachable()
end

const DegreesT = SmallV{Pair{SmallV{Symbol}, Float64}}
const RODegreesT = ReadOnlyVector{Pair{SmallV{Symbol}, Float64}, DegreesT}

@cache function _get_degrees_1(expr::BasicSymbolic{SymReal})::RODegreesT
    __get_degrees(expr)
end
@cache function _get_degrees_2(expr::BasicSymbolic{SafeReal})::RODegreesT
    __get_degrees(expr)
end
@cache function _get_degrees_3(expr::BasicSymbolic{TreeReal})::RODegreesT
    __get_degrees(expr)
end

function __default_degrees!(degrees::DegreesT, expr::BasicSymbolic{T}) where {T}
    push!(degrees, SmallV{Symbol}((Symbol(:zzzzzzz, hash(expr)),)) => 1.0)
end

function __get_degrees(expr::BasicSymbolic{T})::RODegreesT where {T}
    degrees = DegreesT()
    @match expr begin
        BSImpl.Const(;) => return RODegreesT(degrees)
        BSImpl.Sym(; name) => return RODegreesT(push!(degrees, SmallV{Symbol}((name,)) => 1.0))
        BSImpl.Term(; f, args) => begin
            if f === (^)
                base, pow = args
                if isconst(pow) && (_pow = unwrap_const(pow)) isa Real
                    # Powers can be made `Float64` because we don't care about accuracy,
                    # just relative ordering. Also absurdly large powers are arguably rare
                    # enough that we don't mind them being `Inf`.
                    _pow = convert(Float64, _pow)
                    base_degs = copy(parent(get_degrees(base)))
                    @union_split_smallvec base_degs begin
                        # Multiply degrees by `_pow`
                        for (i, deg) in enumerate(base_degs)
                            base_degs[i] = deg[1] => (deg[2] * _pow)
                        end
                        # If `_pow` is negative, we re-sort
                        if _pow < 0 && length(base_degs) > 1
                            sort!(base_degs)
                        end
                    end
                    return RODegreesT(base_degs)
                else
                    return RODegreesT(__default_degrees!(degrees, expr))
                end
            elseif f === getindex
                syms = SmallV{Symbol}()
                sizehint!(syms, length(args))
                @union_split_smallvec args begin
                    for arg in args
                        if isconst(arg)
                            push!(syms, index_arg_to_symbol(arg))
                            continue
                        end
                        arg_deg = parent(get_degrees(arg))
                        @union_split_smallvec arg_deg begin
                            for (_syms, _) in arg_deg
                                append!(syms, _syms)
                            end
                        end
                    end
                end
                push!(degrees, syms => 1.0)
                return RODegreesT(degrees)
            else
                return RODegreesT(__default_degrees!(degrees, expr))
            end
        end
        BSImpl.Div(; num, den) => begin
            if isconst(den)
                return get_degrees(num)
            elseif isconst(num)
                degs = copy(parent(get_degrees(den)))
                @union_split_smallvec degs begin
                    for (i, deg) in enumerate(degs)
                        degs[i] = deg[1] => -deg[2]
                    end
                    sort!(degs)
                end
                return RODegreesT(degs)
            else
                return RODegreesT(__default_degrees!(degrees, expr))
            end
        end
        BSImpl.AddMul(; variant, dict) => begin
            if variant === AddMulVariant.ADD
                cur_degsum = 0
                # Technically we want to call `_get_degrees` on `arguments(..)` but since
                # constants don't contribute to the result, it is equivalent to calling
                # `_get_degrees` on `keys(dict)`.
                for k in keys(dict)
                    kdegs = parent(get_degrees(k))
                    kdegsum = sum(last, kdegs)
                    if isempty(degrees) || kdegsum > cur_degsum ||
                        kdegsum == cur_degsum && lexlt(kdegs, degrees)
                        degrees = kdegs
                        cur_degsum = kdegsum
                    end
                end
                return RODegreesT(degrees)
            else
                # For multiplication, we just use `arguments` since otherwise we'd need to
                # duplicate the `^` code.
                args = parent(arguments(expr))
                sizehint!(degrees, length(args))
                @union_split_smallvec args begin
                    for arg in args
                        append!(degrees, get_degrees(arg))
                    end
                end
                @union_split_smallvec degrees sort!(degrees)
                return RODegreesT(degrees)
            end
        end
        BSImpl.ArrayOp(;) => return RODegreesT(__default_degrees!(degrees, expr))
    end
end

function index_arg_to_symbol(x::BasicSymbolic{T})::Symbol where {T}
    x = unwrap_const(x)
    if x isa Int
        return Symbol(x)
    elseif x isa Colon
        return Symbol(x)
    elseif x isa UnitRange{Int}
        return Symbol(x)
    elseif x isa StepRange{Int, Int}
        return Symbol(x)
    else
        return Symbol(x)::Symbol
    end
end

function monomial_lt(degs1::RODegreesT, degs2::RODegreesT)
    monomial_lt(parent(degs1), parent(degs2))
end

function monomial_lt(degs1::DegreesT, degs2::DegreesT)
    @union_split_smallvec degs1 begin
        @union_split_smallvec degs2 begin
            d1 = sum(last, degs1; init=0.0)
            d2 = sum(last, degs2; init=0.0)
            d1 != d2 ?
                # lower absolute degree first, or if equal, positive degree first
                (abs(d1) < abs(d2) || abs(d1) == abs(d2) && d1 > d2) :
                lexlt(degs1, degs2)
        end
    end
end

function lexlt(degs1::AbstractVector{eltype(DegreesT)}, degs2::AbstractVector{eltype(DegreesT)})
    for ((a_base, a_deg), (b_base, b_deg)) in zip(degs1, degs2)
        if a_base == b_base && a_deg != b_deg
            # same base, higher absolute degree first, positive degree first
            return abs(a_deg) > abs(b_deg) || abs(a_deg) == abs(b_deg) && a_deg > b_deg
        elseif a_base != b_base
            # lexicographic order for the base
            return a_base < b_base
        end
    end
    return false # they are equal
end
function lexlt(degs1::DegreesT, degs2::DegreesT)
    @union_split_smallvec degs1 begin
        @union_split_smallvec degs2 begin
            return lexlt(degs1, degs2)
        end
    end
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
function <ₑ(a::RODegreesT, b::RODegreesT)
    <ₑ(parent(a), parent(b))
end
function <ₑ(a::DegreesT, b::RODegreesT)
    <ₑ(a, parent(b))
end
function <ₑ(a::RODegreesT, b::DegreesT)
    <ₑ(parent(a), b)
end
function <ₑ(a::DegreesT, b::DegreesT)
    @union_split_smallvec a begin
        @union_split_smallvec b begin
            for (x, y) in zip(a, b)
                if x <ₑ y
                    return true
                elseif y <ₑ x
                    return false
                end
            end
            return length(a) < length(b)
        end
    end
end

function <ₑ(a::BasicSymbolic, b::BasicSymbolic)
    if isconst(a) || isconst(b)
        return <ₑ(unwrap_const(a), unwrap_const(b))
    end
    da, db = get_degrees(a), get_degrees(b)
    fw = monomial_lt(da, db)
    bw = monomial_lt(db, da)
    if fw === bw && !isequal(a, b)
        if _arglen(a) == _arglen(b) != 0
            return (operation(a), arguments(a)...,) <ₑ (operation(b), arguments(b)...,)
        else
            return _arglen(a) < _arglen(b)
        end
    else
        return fw
    end
end
