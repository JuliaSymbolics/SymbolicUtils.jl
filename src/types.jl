#-------------------
#--------------------
#### Symbolic
#--------------------
abstract type Symbolic{T} end

###
### Uni-type design
###

@enum ExprType::UInt8  SYM TERM ADD MUL POW DIV

const Metadata = Union{Nothing,Base.ImmutableDict{DataType,Any}}
const NO_METADATA = nothing

sdict(kv...) = Dict{Any, Any}(kv...)

using Base: RefValue
const EMPTY_ARGS = []
const EMPTY_HASH = RefValue(UInt(0))
const NOT_SORTED = RefValue(false)
const EMPTY_DICT = sdict()
const EMPTY_DICT_T = typeof(EMPTY_DICT)

@compactify show_methods=false begin
    @abstract struct BasicSymbolic{T} <: Symbolic{T}
        metadata::Metadata     = NO_METADATA
    end
    struct Sym{T} <: BasicSymbolic{T}
        name::Symbol           = :OOF
    end
    struct Term{T} <: BasicSymbolic{T}
        f::Any                 = identity  # base/num if Pow; issorted if Add/Dict
        arguments::Vector{Any} = EMPTY_ARGS
        hash::RefValue{UInt}   = EMPTY_HASH
    end
    struct Mul{T} <: BasicSymbolic{T}
        coeff::Any             = 0         # exp/den if Pow
        dict::EMPTY_DICT_T     = EMPTY_DICT
        hash::RefValue{UInt}   = EMPTY_HASH
        arguments::Vector{Any} = EMPTY_ARGS
        issorted::RefValue{Bool} = NOT_SORTED
    end
    struct Add{T} <: BasicSymbolic{T}
        coeff::Any             = 0         # exp/den if Pow
        dict::EMPTY_DICT_T     = EMPTY_DICT
        hash::RefValue{UInt}   = EMPTY_HASH
        arguments::Vector{Any} = EMPTY_ARGS
        issorted::RefValue{Bool} = NOT_SORTED
    end
    struct Div{T} <: BasicSymbolic{T}
        num::Any               = 1
        den::Any               = 1
        simplified::Bool       = false
        arguments::Vector{Any} = EMPTY_ARGS
    end
    struct Pow{T} <: BasicSymbolic{T}
        base::Any              = 1
        exp::Any               = 1
        arguments::Vector{Any} = EMPTY_ARGS
    end
end

function exprtype(x::BasicSymbolic)
    @compactified x::BasicSymbolic begin
        Term => TERM
        Add  => ADD
        Mul  => MUL
        Div  => DIV
        Pow  => POW
        Sym  => SYM
        _    => error_on_type()
    end
end

# Same but different error messages
@noinline error_on_type() = error("Internal error: unreachable reached!")
@noinline error_sym() = error("Sym doesn't have a operation or arguments!")
@noinline error_property(E, s) = error("$E doesn't have field $s")

# We can think about bits later
# flags
const SIMPLIFIED = 0x01 << 0

#@inline is_of_type(x::BasicSymbolic, type::UInt8) = (x.bitflags & type) != 0x00
#@inline issimplified(x::BasicSymbolic) = is_of_type(x, SIMPLIFIED)

function ConstructionBase.setproperties_object(obj::BasicSymbolic{T}, patch)::BasicSymbolic{T} where T
    nt = getproperties(obj)
    nt_new = merge(nt, patch)
    Unityper.rt_constructor(obj){T}(;nt_new...)
end

###
### Term interface
###
symtype(x::Number) = typeof(x)
@inline symtype(::Symbolic{T}) where T = T

# We're returning a function pointer
@inline function operation(x::BasicSymbolic)
    @compactified x::BasicSymbolic begin
        Term => x.f
        Add  => (+)
        Mul  => (*)
        Div  => (/)
        Pow  => (^)
        Sym  => error_sym()
        _    => error_on_type()
    end
end

function arguments(x::BasicSymbolic)
    args = unsorted_arguments(x)
    @compactified x::BasicSymbolic begin
        Add => @goto ADDMUL
        Mul => @goto ADDMUL
        _   => return args
    end
    @label ADDMUL
    if !x.issorted[]
        sort!(args, lt = <ₑ)
        x.issorted[] = true
    end
    return args
end
function unsorted_arguments(x::BasicSymbolic)
    @compactified x::BasicSymbolic begin
        Term => return x.arguments
        Add  => @goto ADDMUL
        Mul  => @goto ADDMUL
        Div  => @goto DIV
        Pow  => @goto POW
        Sym  => error_sym()
        _    => error_on_type()
    end

    @label ADDMUL
    E = exprtype(x)
    args = x.arguments
    isempty(args) || return args
    siz = length(x.dict)
    idcoeff = E === ADD ? iszero(x.coeff) : isone(x.coeff)
    sizehint!(args, idcoeff ? siz : siz + 1)
    idcoeff || push!(args, x.coeff)
    if isadd(x)
        for (k, v) in x.dict
            push!(args, applicable(*,k,v) ? k*v :
                    similarterm(k, *, [k, v]))
        end
    else # MUL
        for (k, v) in x.dict
            push!(args, unstable_pow(k, v))
        end
    end
    return args

    @label DIV
    args = x.arguments
    isempty(args) || return args
    sizehint!(args, 2)
    push!(args, x.num)
    push!(args, x.den)
    return args

    @label POW
    args = x.arguments
    isempty(args) || return args
    sizehint!(args, 2)
    push!(args, x.base)
    push!(args, x.exp)
    return args
end

istree(s::BasicSymbolic) = !issym(s)
@inline isa_SymType(T::Val{S}, x) where {S} = x isa BasicSymbolic ? Unityper.isa_type_fun(Val(SymbolicUtils.BasicSymbolic), T, x) : false
issym(x::BasicSymbolic) = isa_SymType(Val(:Sym), x)
isterm(x) = isa_SymType(Val(:Term), x)
ismul(x)  = isa_SymType(Val(:Mul), x)
isadd(x)  = isa_SymType(Val(:Add), x)
ispow(x)  = isa_SymType(Val(:Pow), x)
isdiv(x)  = isa_SymType(Val(:Div), x)

###
### Base interface
###

Base.isequal(::Symbolic, x) = false
Base.isequal(x, ::Symbolic) = false
Base.isequal(::Symbolic, ::Symbolic) = false
coeff_isequal(a, b) = isequal(a, b) || ((a isa AbstractFloat || b isa AbstractFloat) && (a==b))
function Base.isequal(a::BasicSymbolic{T}, b::BasicSymbolic{S}) where {T,S}
    a === b && return true

    E = exprtype(a)
    E === exprtype(b) || return false

    T === S || return false

    if E === SYM
        nameof(a) === nameof(b)
    elseif E === ADD || E === MUL
        coeff_isequal(a.coeff, b.coeff) && isequal(a.dict, b.dict)
    elseif E === DIV
        isequal(a.num, b.num) && isequal(a.den, b.den)
    elseif E === POW
        isequal(a.exp, b.exp) && isequal(a.base, b.base)
    elseif E === TERM
        a1 = arguments(a)
        a2 = arguments(b)
        isequal(operation(a), operation(b)) &&
            length(a1) == length(a2) &&
            all(isequal(l, r) for (l, r) in zip(a1, a2))
    else
        error_on_type()
    end
end

Base.one( s::Symbolic) = one( symtype(s))
Base.zero(s::Symbolic) = zero(symtype(s))

Base.nameof(s::BasicSymbolic) = issym(s) ? s.name : error("None Sym BasicSymbolic doesn't have a name")

## This is much faster than hash of an array of Any
hashvec(xs, z) = foldr(hash, xs, init=z)
function Base.hash(s::BasicSymbolic, salt::UInt)
    E = exprtype(s)
    if E === SYM
        hash(nameof(s), salt ⊻ 0x4de7d7c66d41da43)
    elseif E === ADD || E === MUL
        !iszero(salt) && return hash(hash(s, zero(UInt64)), salt)
        h = s.hash[]
        !iszero(h) && return h
        hashoffset = isadd(s) ? 0xaddaddaddaddadda : 0xaaaaaaaaaaaaaaaa
        h′= hash(hashoffset, hash(s.coeff, hash(s.dict, salt)))
        s.hash[] = h′
        return h′
    elseif E === DIV
        return hash(s.num, hash(s.den, salt ⊻ 0x334b218e73bbba53))
    elseif E === POW
        hash(s.exp, hash(s.base, salt ⊻ 0x2b55b97a6efb080c))
    elseif E === TERM
        !iszero(salt) && return hash(hash(s, zero(UInt)), salt)
        h = s.hash[]
        !iszero(h) && return h
        op = operation(s)
        oph = op isa Function ? nameof(op) : op
        h′ = hashvec(arguments(s), hash(oph, salt))
        s.hash[] = h′
        return h′
    else
        error_on_type()
    end
end

###
### Constructors
###

function Sym{T}(name::Symbol; kw...) where T
    Sym{T}(; name=name, kw...)
end

function Term{T}(f, args; kw...) where T
    if eltype(args) !== Any
        args = convert(Vector{Any}, args)
    end

    Term{T}(;f=f, arguments=args, hash=Ref(UInt(0)), kw...)
end

function Term(f, args; metadata=NO_METADATA)
    Term{_promote_symtype(f, args)}(f, args, metadata=metadata)
end

function Add(::Type{T}, coeff, dict; metadata=NO_METADATA, kw...) where T
    if isempty(dict)
        return coeff
    elseif _iszero(coeff) && length(dict) == 1
        k,v = first(dict)
        if _isone(v)
            return k
        else
            coeff, dict = makemul(v, k)
            return Mul(T, coeff, dict)
        end
    end

    Add{T}(; coeff, dict, hash=Ref(UInt(0)), metadata, arguments=[], issorted=RefValue(false), kw...)
end

function Mul(T, a, b; metadata=NO_METADATA, kw...)
    isempty(b) && return a
    if _isone(a) && length(b) == 1
        pair = first(b)
        if _isone(last(pair)) # first value
            return first(pair)
        else
            return unstable_pow(first(pair), last(pair))
        end
    else
        coeff = a
        dict = b
        Mul{T}(; coeff, dict, hash=Ref(UInt(0)), metadata, arguments=[], issorted=RefValue(false), kw...)
    end
end

const Rat = Union{Rational, Integer}

function ratcoeff(x)
    if ismul(x)
        ratcoeff(x.coeff)
    elseif x isa Rat
        (true, x)
    else
        (false, NaN)
    end
end
ratio(x::Integer,y::Integer) = iszero(rem(x,y)) ? div(x,y) : x//y
ratio(x::Rat,y::Rat) = x//y
function maybe_intcoeff(x)
    if ismul(x)
        if x.coeff isa Rational && isone(x.coeff.den)
            Mul{symtype(x)}(; coeff=x.coeff.num, dict=x.dict, x.metadata, arguments=[], issorted=RefValue(false))
        else
            x
        end
    elseif x isa Rational
        isone(x.den) ? x.num : x
    else
        x
    end
end

function Div{T}(n, d, simplified=false; metadata=nothing) where {T}
    if T<:Number && !(T<:SafeReal)
        n, d = quick_cancel(n, d)
    end
    _iszero(n) && return zero(typeof(n))
    _isone(d) && return n

    if isdiv(n) && isdiv(d)
        return Div{T}(n.num * d.den, n.den * d.num)
    elseif isdiv(n)
        return Div{T}(n.num, n.den * d)
    elseif isdiv(d)
        return Div{T}(n * d.den, d.num)
    end

    d isa Number && _isone(-d) && return -1 * n
    n isa Rat && d isa Rat && return n // d # maybe called by oblivious code in simplify

    # GCD coefficient upon construction
    rat, nc = ratcoeff(n)
    if rat
        rat, dc = ratcoeff(d)
        if rat
            g = gcd(nc, dc) * sign(dc) # make denominator positive
            invdc = ratio(1, g)
            n = maybe_intcoeff(invdc * n)
            d = maybe_intcoeff(invdc * d)
            if d isa Number
                _isone(d) && return n
                _isone(-d) && return -1 * n
            end
        end
    end

    Div{T}(; num=n, den=d, simplified, arguments=[], metadata)
end

function Div(n,d, simplified=false; kw...)
    Div{promote_symtype((/), symtype(n), symtype(d))}(n, d, simplified; kw...)
end

@inline function numerators(x)
    isdiv(x) && return numerators(x.num)
    istree(x) && operation(x) === (*) ? arguments(x) : Any[x]
end

@inline denominators(x) = isdiv(x) ? numerators(x.den) : Any[1]

function (::Type{<:Pow{T}})(a, b; metadata=NO_METADATA) where {T}
    _iszero(b) && return 1
    _isone(b) && return a
    Pow{T}(; base=a, exp=b, arguments=[], metadata)
end

function Pow(a, b; metadata=NO_METADATA)
    Pow{promote_symtype(^, symtype(a), symtype(b))}(makepow(a, b)..., metadata=metadata)
end

function toterm(t::BasicSymbolic{T}) where T
    E = exprtype(t)
    if E === SYM || E === TERM
        return t
    elseif E === ADD || E === MUL
        args = Any[]
        push!(args, t.coeff)
        for (k, coeff) in t.dict
            push!(args, coeff == 1 ? k : Term{T}(E === MUL ? (^) : (*), Any[coeff, k]))
        end
        Term{T}(operation(t), args)
    elseif E === DIV
        Term{T}(/, Any[t.num, t.den])
    elseif E === POW
        Term{T}(^, [t.base, t.exp])
    else
        error_on_type()
    end
end

"""
    makeadd(sign, coeff::Number, xs...)

Any Muls inside an Add should always have a coeff of 1
and the key (in Add) should instead be used to store the actual coefficient
"""
function makeadd(sign, coeff, xs...)
    d = sdict()
    for x in xs
        if isadd(x)
            coeff += x.coeff
            _merge!(+, d, x.dict, filter=_iszero)
            continue
        end
        if x isa Number
            coeff += x
            continue
        end
        if ismul(x)
            k = Mul(symtype(x), 1, x.dict)
            v = sign * x.coeff + get(d, k, 0)
        else
            k = x
            v = sign + get(d, x, 0)
        end
        if iszero(v)
            delete!(d, k)
        else
            d[k] = v
        end
    end
    coeff, d
end

function makemul(coeff, xs...; d=sdict())
    for x in xs
        if ispow(x) && x.exp isa Number
            d[x.base] = x.exp + get(d, x.base, 0)
        elseif x isa Number
            coeff *= x
        elseif ismul(x)
            coeff *= x.coeff
            _merge!(+, d, x.dict, filter=_iszero)
        else
            v = 1 + get(d, x, 0)
            if _iszero(v)
                delete!(d, x)
            else
                d[x] = v
            end
        end
    end
    (coeff, d)
end

unstable_pow(a, b) = a isa Integer && b isa Integer ? (a//1) ^ b : a ^ b

function makepow(a, b)
    base = a
    exp = b
    if ispow(a)
        base = a.base
        exp = a.exp * b
    end
    return (base, exp)
end

function term(f, args...; type = nothing)
    if type === nothing
        T = _promote_symtype(f, args)
    else
        T = type
    end
    Term{T}(f, Any[args...])
end

"""
    unflatten(t::Symbolic{T})
Binarizes `Term`s with n-ary operations
"""
function unflatten(t::Symbolic{T}) where{T}
    if istree(t)
        f = operation(t)
        if f == (+) || f == (*)   # TODO check out for other n-ary --> binary ops
            a = arguments(t)
            return foldl((x,y) -> Term{T}(f, Any[x, y]), a)
        end
    end
    return t
end

unflatten(t) = t

"""
    similarterm(t, f, args, symtype; metadata=nothing)

Create a term that is similar in type to `t`. Extending this function allows packages
using their own expression types with SymbolicUtils to define how new terms should
be created. Note that `similarterm` may return an object that has a
different type than `t`, because `f` also influences the result.

## Arguments

- `t` the reference term to use to create similar terms
- `f` is the operation of the term
- `args` is the arguments
- The `symtype` of the resulting term. Best effort will be made to set the symtype of the
  resulting similar term to this type.
"""
similarterm(t::Symbolic, f, args; metadata=nothing) =
    similarterm(t, f, args, _promote_symtype(f, args); metadata=metadata)
similarterm(t::BasicSymbolic, f, args,
            symtype; metadata=nothing) = basic_similarterm(t, f, args, symtype; metadata=metadata)

function basic_similarterm(t, f, args, stype; metadata=nothing)
    if f isa Symbol
        error("$f must not be a Symbol")
    end
    T = stype
    if T === nothing
        T = _promote_symtype(f, args)
    end
    if T <: LiteralReal
        Term{T}(f, args, metadata=metadata)
    elseif stype <: Number && (f in (+, *) || (f in (/, ^) && length(args) == 2)) && all(x->symtype(x) <: Number, args)
        res = f(args...)
        if res isa Symbolic
            @set! res.metadata = metadata
        end
        return res
    else
        Term{T}(f, args, metadata=metadata)
    end
end

###
### Tree print
###

import AbstractTrees

struct TreePrint
    op
    x
end

function AbstractTrees.children(x::BasicSymbolic)
    if isterm(x) || ispow(x)
        return arguments(x)
    elseif isadd(x) || ismul(x)
        children = Any[x.coeff]
        for (key, coeff) in pairs(x.dict)
            if coeff == 1
                push!(children, key)
            else
                push!(children, TreePrint(isadd(x) ? (:*) : (:^), (key, coeff)))
            end
        end
        return children
    end
end

AbstractTrees.children(x::TreePrint) = [x.x[1], x.x[2]]

print_tree(x; show_type=false, maxdepth=Inf, kw...) = print_tree(stdout, x; show_type=show_type, maxdepth=maxdepth, kw...)

function print_tree(_io::IO, x::BasicSymbolic; show_type=false, kw...)
    if isterm(x) || isadd(x) || ismul(x) || ispow(x) || isdiv(x)
        AbstractTrees.print_tree(_io, x; withinds=true, kw...) do io, y, inds
            if istree(y)
                print(io, operation(y))
            elseif y isa TreePrint
                print(io, "(", y.op, ")")
            else
                print(io, y)
            end
            if !(y isa TreePrint) && show_type
                print(io, " [", typeof(y), "]")
            end
        end
    end
end

###
### Metadata
###
metadata(s::Symbolic) = s.metadata
metadata(s::Symbolic, meta) = Setfield.@set! s.metadata = meta

function hasmetadata(s::Symbolic, ctx)
    metadata(s) isa AbstractDict && haskey(metadata(s), ctx)
end

function getmetadata(s::Symbolic, ctx)
    md = metadata(s)
    if md isa AbstractDict
        md[ctx]
    else
        throw(ArgumentError("$s does not have metadata for $ctx"))
    end
end

function getmetadata(s::Symbolic, ctx, default)
    md = metadata(s)
    md isa AbstractDict ? get(md, ctx, default) : default
end

# pirated for Setfield purposes:
using Base: ImmutableDict
Base.ImmutableDict(d::ImmutableDict{K,V}, x, y)  where {K, V} = ImmutableDict{K,V}(d, x, y)

assocmeta(d::Dict, ctx, val) = (d=copy(d); d[ctx] = val; d)
function assocmeta(d::Base.ImmutableDict, ctx, val)::ImmutableDict{DataType,Any}
    # optimizations
    # If using upto 3 contexts, things stay compact
    if isdefined(d, :parent)
        d.key === ctx && return @set d.value = val
        d1 = d.parent
        if isdefined(d1, :parent)
            d1.key === ctx && return @set d.parent.value = val
            d2 = d1.parent
            if isdefined(d2, :parent)
                d2.key === ctx && return @set d.parent.parent.value = val
            end
        end
    end
    Base.ImmutableDict{DataType, Any}(d, ctx, val)
end

function setmetadata(s::Symbolic, ctx::DataType, val)
    if s.metadata isa AbstractDict
        @set s.metadata = assocmeta(s.metadata, ctx, val)
    else
        # fresh Dict
        @set s.metadata = Base.ImmutableDict{DataType, Any}(ctx, val)
    end
end


function to_symbolic(x)
    Base.depwarn("`to_symbolic(x)` is deprecated, define the interface for your " *
                 "symbolic structure using `istree(x)`, `operation(x)`, `arguments(x)` " *
                 "and `similarterm(::YourType, f, args, symtype)`", :to_symbolic, force=true)

    x
end

###
###  Pretty printing
###
const show_simplified = Ref(false)

isnegative(t::Real) = t < 0
function isnegative(t)
    if istree(t) && operation(t) === (*)
        coeff = first(arguments(t))
        return isnegative(coeff)
    end
    return false
end

# Term{}
setargs(t, args) = Term{symtype(t)}(operation(t), args)
cdrargs(args) = setargs(t, cdr(args))

print_arg(io, x::Union{Complex, Rational}; paren=true) = print(io, "(", x, ")")
isbinop(f) = istree(f) && !istree(operation(f)) && Base.isbinaryoperator(nameof(operation(f)))
function print_arg(io, x; paren=false)
    if paren && isbinop(x)
        print(io, "(", x, ")")
    else
        print(io, x)
    end
end
print_arg(io, s::String; paren=true) = show(io, s)
function print_arg(io, f, x)
    f !== (*) && return print_arg(io, x)
    if Base.isbinaryoperator(nameof(f))
        print_arg(io, x, paren=true)
    else
        print_arg(io, x)
    end
end

function remove_minus(t)
    !istree(t) && return -t
    @assert operation(t) == (*)
    args = arguments(t)
    @assert args[1] < 0
    Any[-args[1], args[2:end]...]
end

function show_add(io, args)
    negs = filter(isnegative, args)
    nnegs = filter(!isnegative, args)
    for (i, t) in enumerate(nnegs)
        i != 1 && print(io, " + ")
        print_arg(io, +,  t)
    end

    for (i, t) in enumerate(negs)
        if i==1 && isempty(nnegs)
            print_arg(io, -, t)
        else
            print(io, " - ")
            show_mul(io, remove_minus(t))
        end
    end
end

function show_pow(io, args)
    base, ex = args

    if base isa Real && base < 0
        print(io, "(")
        print_arg(io, base)
        print(io, ")")
    else
        print_arg(io, base, paren=true)
    end
    print(io, "^")
    print_arg(io, ex, paren=true)
end

function show_mul(io, args)
    length(args) == 1 && return print_arg(io, *, args[1])

    minus = args[1] isa Number && args[1] == -1
    unit = args[1] isa Number && args[1] == 1

    paren_scalar = (args[1] isa Complex && !_iszero(imag(args[1]))) ||
                   args[1] isa Rational ||
                   (args[1] isa Number && !isfinite(args[1]))

    nostar = minus || unit ||
            (!paren_scalar && args[1] isa Number && !(args[2] isa Number))

    for (i, t) in enumerate(args)
        if i != 1
            if i==2 && nostar
            else
                print(io, "*")
            end
        end
        if i == 1 && minus
            print(io, "-")
        elseif i == 1 && unit
        else
            print_arg(io, *, t)
        end
    end
end

function show_ref(io, f, args)
    x = args[1]
    idx = args[2:end]

    istree(x) && print(io, "(")
    print(io, x)
    istree(x) && print(io, ")")
    print(io, "[")
    for i=1:length(idx)
        print_arg(io, idx[i])
        i != length(idx) && print(io, ", ")
    end
    print(io, "]")
end

function show_call(io, f, args)
    fname = istree(f) ? Symbol(repr(f)) : nameof(f)
    len_args = length(args)
    if Base.isunaryoperator(fname) && len_args == 1
        print(io, "$fname")
        print_arg(io, first(args), paren=true)
    elseif Base.isbinaryoperator(fname) && len_args > 1
        for (i, t) in enumerate(args)
            i != 1 && print(io, " $fname ")
            print_arg(io, t, paren=true)
        end
    else
        if issym(f)
            Base.show_unquoted(io, nameof(f))
        else
            Base.show(io, f)
        end
        print(io, "(")
        for i=1:length(args)
            print(io, args[i])
            i != length(args) && print(io, ", ")
        end
        print(io, ")")
    end
end

function show_term(io::IO, t)
    if get(io, :simplify, show_simplified[])
        return print(IOContext(io, :simplify=>false), simplify(t))
    end

    f = operation(t)
    args = arguments(t)

    if f === (+)
        show_add(io, args)
    elseif f === (*)
        show_mul(io, args)
    elseif f === (^)
        show_pow(io, args)
    elseif f === (getindex)
        show_ref(io, f, args)
    elseif f === (identity) && !issym(args[1]) && !istree(args[1])
        show(io, args[1])
    else
        show_call(io, f, args)
    end

    return nothing
end

showraw(io, t) = Base.show(IOContext(io, :simplify=>false), t)
showraw(t) = showraw(stdout, t)

function Base.show(io::IO, v::BasicSymbolic)
    if issym(v)
        Base.show_unquoted(io, v.name)
    else
        show_term(io, v)
    end
end

###
### Symbolic function / type inference
###

"""
    promote_symtype(f, Ts...)

The result of applying `f` to arguments of [`symtype`](#symtype) `Ts...`

```julia
julia> promote_symtype(+, Real, Real)
Real

julia> promote_symtype(+, Complex, Real)
Number

julia> @syms f(x)::Complex
(f(::Number)::Complex,)

julia> promote_symtype(f, Number)
Complex
```

When constructing [`Term`](#Term)s without an explicit symtype,
`promote_symtype` is used to figure out the symtype of the Term.
"""
promote_symtype(f, Ts...) = Any

#---------------------------
#---------------------------
#### Function-like variables
#---------------------------

struct FnType{X<:Tuple,Y} end

(f::Symbolic{<:FnType})(args...) = Term{promote_symtype(f, symtype.(args)...)}(f, Any[args...])

function (f::Symbolic)(args...)
    error("Sym $f is not callable. " *
          "Use @syms $f(var1, var2,...) to create it as a callable.")
end

"""
    promote_symtype(f::FnType{X,Y}, arg_symtypes...)

The output symtype of applying variable `f` to arugments of symtype `arg_symtypes...`.
if the arguments are of the wrong type then this function will error.
"""
function promote_symtype(f::BasicSymbolic{<:FnType{X,Y}}, args...) where {X, Y}
    if X === Tuple
        return Y
    end

    # This is to handle `Tuple{T} where T`, so we cannot reliably query the type
    # parameters of the `Tuple` in `FnType`.
    t = Tuple{args...}
    if !(t <: X)
        error("$t is not a subtype of $X.")
    end
    return Y
end

function Base.show(io::IO, f::Symbolic{<:FnType{X,Y}}) where {X,Y}
    print(io, nameof(f))
    # Use `Base.unwrap_unionall` to handle `Tuple{T} where T`. This is not the
    # best printing, but it's better than erroring.
    argrepr = join(map(t->"::"*string(t), Base.unwrap_unionall(X).parameters), ", ")
    print(io, "(", argrepr, ")")
    print(io, "::", Y)
end

@inline isassociative(op) = op === (+) || op === (*)

function _promote_symtype(f, args)
    if issym(f)
        promote_symtype(f, map(symtype, args)...)
    else
        if length(args) == 0
            promote_symtype(f)
        elseif length(args) == 1
            promote_symtype(f, symtype(args[1]))
        elseif length(args) == 2
            promote_symtype(f, symtype(args[1]), symtype(args[2]))
        elseif isassociative(f)
            mapfoldl(symtype, (x,y) -> promote_symtype(f, x, y), args)
        else
            promote_symtype(f, map(symtype, args)...)
        end
    end
end

###
### Macro
###

"""
    @syms <lhs_expr>[::T1] <lhs_expr>[::T2]...

For instance:

    @syms foo::Real bar baz(x, y::Real)::Complex

Create one or more variables. `<lhs_expr>` can be just a symbol in which case
it will be the name of the variable, or a function call in which case a function-like
variable which has the same name as the function being called. The Sym type, or
in the case of a function-like Sym, the output type of calling the function
can be set using the `::T` syntax.

# Examples:

- `@syms foo bar::Real baz::Int` will create
variable `foo` of symtype `Number` (the default), `bar` of symtype `Real`
and `baz` of symtype `Int`
- `@syms f(x) g(y::Real, x)::Int h(a::Int, f(b))` creates 1-arg `f` 2-arg `g`
and 2 arg `h`. The second argument to `h` must be a one argument function-like
variable. So, `h(1, g)` will fail and `h(1, f)` will work.
"""
macro syms(xs...)
    defs = map(xs) do x
        n, t = _name_type(x)
        T = esc(t)
        nt = _name_type(x)
        n, t = nt.name, nt.type
        :($(esc(n)) = Sym{$T}($(Expr(:quote, n))))
    end
    Expr(:block, defs...,
         :(tuple($(map(x->esc(_name_type(x).name), xs)...))))
end

function syms_syntax_error()
    error("Incorrect @syms syntax. Try `@syms x::Real y::Complex g(a) f(::Real)::Real` for instance.")
end

function _name_type(x)
    if x isa Symbol
        return (name=x, type=Number)
    elseif x isa Expr && x.head === :(::)
        if length(x.args) == 1
            return (name=nothing, type=x.args[1])
        end
        lhs, rhs = x.args[1:2]
        if lhs isa Expr && lhs.head === :call
            # e.g. f(::Real)::Unreal
            type = map(x->_name_type(x).type, lhs.args[2:end])
            return (name=lhs.args[1], type=:($FnType{Tuple{$(type...)}, $rhs}))
        else
            return (name=lhs, type=rhs)
        end
    elseif x isa Expr && x.head === :ref
        ntype = _name_type(x.args[1]) # a::Number
        N = length(x.args)-1
        return (name=ntype.name,
                type=:(Array{$(ntype.type), $N}),
                array_metadata=:(Base.Slice.(($(x.args[2:end]...),))))
    elseif x isa Expr && x.head === :call
        return _name_type(:($x::Number))
    else
        syms_syntax_error()
    end
end

###
### Arithmetic
###
const SN = Symbolic{<:Number}
# integration. Constructors of `Add, Mul, Pow...` from Base (+, *, ^, ...)

_merge(f::F, d, others...; filter=x->false) where F = _merge!(f, Dict{Any,Any}(d), others...; filter=filter)

function _merge!(f::F, d, others...; filter=x->false) where F
    acc = d
    for other in others
        for (k, v) in other
            v = f(v)
            ak = get(acc, k, nothing)
            if ak !== nothing
                v = ak + v
            end
            if filter(v)
                delete!(acc, k)
            else
                acc[k] = v
            end
        end
    end
    acc
end

function mapvalues(f, d1::AbstractDict)
    d = copy(d1)
    for (k, v) in d
        d[k] = f(k, v)
    end
    d
end

add_t(a::Number,b::Number) = promote_symtype(+, symtype(a), symtype(b))
add_t(a,b) = promote_symtype(+, symtype(a), symtype(b))
sub_t(a,b) = promote_symtype(-, symtype(a), symtype(b))
sub_t(a) = promote_symtype(-, symtype(a))

import Base: (+), (-), (*), (//), (/), (\), (^)
function +(a::SN, b::SN)
    if isadd(a) && isadd(b)
        return Add(add_t(a,b),
                   a.coeff + b.coeff,
                   _merge(+, a.dict, b.dict, filter=_iszero))
    elseif isadd(a)
        coeff, dict = makeadd(1, 0, b)
        return Add(add_t(a,b), a.coeff + coeff, _merge(+, a.dict, dict, filter=_iszero))
    elseif isadd(b)
        return b + a
    end
    coeff, dict = makeadd(1, 0, a, b)
    Add(add_t(a,b), coeff, dict)
end

function +(a::Number, b::SN)
    iszero(a) && return b
    if isadd(b)
        Add(add_t(a,b), a + b.coeff, b.dict)
    else
        Add(add_t(a,b), makeadd(1, a, b)...)
    end
end

+(a::SN, b::Number) = b + a

+(a::SN) = a

function -(a::SN)
    isadd(a) ? Add(sub_t(a), -a.coeff, mapvalues((_,v) -> -v, a.dict)) :
    Add(sub_t(a), makeadd(-1, 0, a)...)
end

function -(a::SN, b::SN)
    isadd(a) && isadd(b) ? Add(sub_t(a,b),
                               a.coeff - b.coeff,
                               _merge(-, a.dict,
                                      b.dict,
                                      filter=_iszero)) : a + (-b)
end

-(a::Number, b::SN) = a + (-b)
-(a::SN, b::Number) = a + (-b)


mul_t(a,b) = promote_symtype(*, symtype(a), symtype(b))
mul_t(a) = promote_symtype(*, symtype(a))

*(a::SN) = a

function *(a::SN, b::SN)
    # Always make sure Div wraps Mul
    if isdiv(a) && isdiv(b)
        Div(a.num * b.num, a.den * b.den)
    elseif isdiv(a)
        Div(a.num * b, a.den)
    elseif isdiv(b)
        Div(a * b.num, b.den)
    elseif ismul(a) && ismul(b)
        Mul(mul_t(a, b),
            a.coeff * b.coeff,
            _merge(+, a.dict, b.dict, filter=_iszero))
    elseif ismul(a) && ispow(b)
        if b.exp isa Number
            Mul(mul_t(a, b),
                a.coeff, _merge(+, a.dict, Base.ImmutableDict(b.base=>b.exp), filter=_iszero))
        else
            Mul(mul_t(a, b),
                a.coeff, _merge(+, a.dict, Base.ImmutableDict(b=>1), filter=_iszero))
        end
    elseif ispow(a) && ismul(b)
        b * a
    else
        Mul(mul_t(a,b), makemul(1, a, b)...)
    end
end

function *(a::Number, b::SN)
    if iszero(a)
        a
    elseif isone(a)
        b
    elseif isdiv(b)
        Div(a*b.num, b.den)
    elseif isone(-a) && isadd(b)
        # -1(a+b) -> -a - b
        T = promote_symtype(+, typeof(a), symtype(b))
        Add(T, b.coeff * a, Dict{Any,Any}(k=>v*a for (k, v) in b.dict))
    else
        Mul(mul_t(a, b), makemul(a, b)...)
    end
end

###
### Div
###

/(a::Union{SN,Number}, b::SN) = Div(a, b)

*(a::SN, b::Number) = b * a

\(a::SN, b::Union{Number, SN}) = b / a

\(a::Number, b::SN) = b / a

/(a::SN, b::Number) = (b isa Integer ? 1//b : inv(b)) * a

//(a::Union{SN, Number}, b::SN) = a / b

//(a::SN, b::T) where {T <: Number} = (one(T) // b) * a


###
### Pow
###

function ^(a::SN, b)
    if b isa Number && iszero(b)
        # fast path
        1
    elseif b isa Number && b < 0
        Div(1, a ^ (-b))
    elseif ismul(a) && b isa Number
        coeff = unstable_pow(a.coeff, b)
        Mul(promote_symtype(^, symtype(a), symtype(b)),
            coeff, mapvalues((k, v) -> b*v, a.dict))
    else
        Pow(a, b)
    end
end

^(a::Number, b::SN) = Pow(a, b)
