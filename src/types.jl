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
const SmallV{T} = SmallVec{T, Vector{T}}
const EMPTY_ARGS = SmallV{Any}()
const EMPTY_HASH = RefValue(UInt(0))
const EMPTY_DICT = sdict()
const EMPTY_DICT_T = typeof(EMPTY_DICT)
const ENABLE_HASHCONSING = Ref(true)

@compactify show_methods=false begin
    @abstract mutable struct BasicSymbolic{T} <: Symbolic{T}
        metadata::Metadata     = NO_METADATA
        id::RefValue{UInt64} = Ref{UInt64}(0)
    end
    mutable struct Sym{T} <: BasicSymbolic{T}
        name::Symbol           = :OOF
    end
    mutable struct Term{T} <: BasicSymbolic{T}
        f::Any                 = identity  # base/num if Pow; issorted if Add/Dict
        arguments::SmallV{Any} = EMPTY_ARGS
        hash::RefValue{UInt}   = EMPTY_HASH
        hash2::RefValue{UInt} = EMPTY_HASH
    end
    mutable struct Mul{T} <: BasicSymbolic{T}
        coeff::Any             = 0         # exp/den if Pow
        dict::EMPTY_DICT_T     = EMPTY_DICT
        hash::RefValue{UInt}   = EMPTY_HASH
        hash2::RefValue{UInt} = EMPTY_HASH
        arguments::SmallV{Any} = EMPTY_ARGS
    end
    mutable struct Add{T} <: BasicSymbolic{T}
        coeff::Any             = 0         # exp/den if Pow
        dict::EMPTY_DICT_T     = EMPTY_DICT
        hash::RefValue{UInt}   = EMPTY_HASH
        hash2::RefValue{UInt} = EMPTY_HASH
        arguments::SmallV{Any} = EMPTY_ARGS
    end
    mutable struct Div{T} <: BasicSymbolic{T}
        num::Any               = 1
        den::Any               = 1
        simplified::Bool       = false
        arguments::SmallV{Any} = EMPTY_ARGS
    end
    mutable struct Pow{T} <: BasicSymbolic{T}
        base::Any              = 1
        exp::Any               = 1
        arguments::SmallV{Any} = EMPTY_ARGS
    end
end

function SymbolicIndexingInterface.symbolic_type(::Type{<:BasicSymbolic})
    ScalarSymbolic()
end

"""
    $(TYPEDSIGNATURES)

Return the inner `Symbolic` wrapped in a non-symbolic subtype. Defaults to
returning the input as-is.
"""
unwrap(x) = x

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

const wvd = TaskLocalValue{WeakValueDict{UInt, BasicSymbolic}}(WeakValueDict{UInt, BasicSymbolic})

# Same but different error messages
@noinline error_on_type() = error("Internal error: unreachable reached!")
@noinline error_sym() = error("Sym doesn't have a operation or arguments!")
@noinline error_property(E, s) = error("$E doesn't have field $s")

# We can think about bits later
# flags
const SIMPLIFIED = 0x01 << 0

#@inline is_of_type(x::BasicSymbolic, type::UInt8) = (x.bitflags & type) != 0x00
#@inline issimplified(x::BasicSymbolic) = is_of_type(x, SIMPLIFIED)

function ConstructionBase.setproperties(obj::BasicSymbolic{T}, patch::NamedTuple)::BasicSymbolic{T} where T
    nt = getproperties(obj)
    nt_new = merge(nt, patch)
    # Call outer constructor because hash consing cannot be applied in inner constructor
    @compactified obj::BasicSymbolic begin
        Sym => Sym{T}(nt_new.name; nt_new...)
        Term => Term{T}(nt_new.f, nt_new.arguments; nt_new..., hash = RefValue(UInt(0)), hash2 = RefValue(UInt(0)), id = Ref{UInt64}(0))
        Add => Add(T, nt_new.coeff, nt_new.dict; nt_new..., hash = RefValue(UInt(0)), hash2 = RefValue(UInt(0)), id = Ref{UInt64}(0))
        Mul => Mul(T, nt_new.coeff, nt_new.dict; nt_new..., hash = RefValue(UInt(0)), hash2 = RefValue(UInt(0)), id = Ref{UInt64}(0))
        Div => Div{T}(nt_new.num, nt_new.den, nt_new.simplified; nt_new..., hash = RefValue(UInt(0)), hash2 = RefValue(UInt(0)), id = Ref{UInt64}(0))
        Pow => Pow{T}(nt_new.base, nt_new.exp; nt_new..., hash = RefValue(UInt(0)), hash2 = RefValue(UInt(0)), id = Ref{UInt64}(0))
        _ => Unityper.rt_constructor(obj){T}(;nt_new...)
    end
end

###
### Term interface
###

"""
$(SIGNATURES)

Returns the [numeric type](https://docs.julialang.org/en/v1/base/numbers/#Standard-Numeric-Types) 
of `x`. By default this is just `typeof(x)`.
Define this for your symbolic types if you want [`SymbolicUtils.simplify`](@ref) to apply rules
specific to numbers (such as commutativity of multiplication). Or such
rules that may be implemented in the future.
"""
symtype(x) = typeof(x)
@inline symtype(::Symbolic{T}) where T = T
@inline symtype(::Type{<:Symbolic{T}}) where T = T

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

@inline head(x::BasicSymbolic) = operation(x)

@cache function TermInterface.sorted_arguments(x::BasicSymbolic)::Vector{Any}
    args = copy(arguments(x))
    @compactified x::BasicSymbolic begin
        Add => @goto ADD
        Mul => @goto MUL
        _   => return args
    end
    @label MUL
    sort!(args, by=get_degrees)
    return args

    @label ADD
    sort!(args, lt = monomial_lt, by=get_degrees)
    return args
end

@deprecate unsorted_arguments(x) arguments(x)

TermInterface.children(x::BasicSymbolic) = arguments(x)
TermInterface.sorted_children(x::BasicSymbolic) = sorted_arguments(x)
function TermInterface.arguments(x::BasicSymbolic)
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
                    maketerm(k, *, [k, v], nothing))
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

isexpr(s::BasicSymbolic) = !issym(s)
iscall(s::BasicSymbolic) = isexpr(s)

@inline isa_SymType(T::Val{S}, x) where {S} = x isa BasicSymbolic ? Unityper.isa_type_fun(Val(SymbolicUtils.BasicSymbolic), T, x) : false

"""
    issym(x)

Returns `true` if `x` is a `Sym`. If true, `nameof` must be defined
on `x` and must return a `Symbol`.
"""
issym(x) = isa_SymType(Val(:Sym), x)
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
Base.isequal(::Symbolic, ::Missing) = false
Base.isequal(::Missing, ::Symbolic) = false
Base.isequal(::Symbolic, ::Symbolic) = false
coeff_isequal(a, b; comparator = isequal) = comparator(a, b) || ((a isa AbstractFloat || b isa AbstractFloat) && (a==b))
function _allarequal(xs, ys; comparator = isequal)::Bool
    N = length(xs)
    length(ys) == N || return false
    for n = 1:N
        comparator(xs[n], ys[n]) || return false
    end
    return true
end

function Base.isequal(a::BasicSymbolic{T}, b::BasicSymbolic{S}) where {T,S}
    a === b && return true
    a.id == b.id && a.id != 0 && return true

    E = exprtype(a)
    E === exprtype(b) || return false

    T === S || return false
    return _isequal(a, b, E)::Bool
end
function _isequal(a, b, E; comparator = isequal)
    if E === SYM
        nameof(a) === nameof(b)
    elseif E === ADD || E === MUL
        coeff_isequal(a.coeff, b.coeff; comparator) && comparator(a.dict, b.dict)
    elseif E === DIV
        comparator(a.num, b.num) && comparator(a.den, b.den)
    elseif E === POW
        comparator(a.exp, b.exp) && comparator(a.base, b.base)
    elseif E === TERM
        a1 = arguments(a)
        a2 = arguments(b)
        comparator(operation(a), operation(b)) && _allarequal(a1, a2; comparator)
    else
        error_on_type()
    end
end

"""
$(TYPEDSIGNATURES)

Checks for equality between two `BasicSymbolic` objects, considering both their
values and metadata.

The default `Base.isequal` function for `BasicSymbolic` only compares their expressions
and ignores metadata. This does not help deal with hash collisions when metadata is 
relevant for distinguishing expressions, particularly in hashing contexts. This function
provides a stricter equality check that includes metadata comparison, preventing
such collisions.

Modifying `Base.isequal` directly breaks numerous tests in `SymbolicUtils.jl` and
downstream packages like `ModelingToolkit.jl`, hence the need for this separate
function.
"""
function isequal_with_metadata(a::BasicSymbolic{T}, b::BasicSymbolic{S})::Bool where {T, S}
    a === b && return true
    a.id == b.id && a.id != 0 && return true

    E = exprtype(a)
    E === exprtype(b) || return false

    T === S || return false
    _isequal(a, b, E; comparator = isequal_with_metadata)::Bool && isequal_with_metadata(metadata(a), metadata(b)) || return false
end

function isequal_with_metadata(a::Symbolic, b::Symbolic)::Bool
    a === b && return true
    typeof(a) == typeof(b) || return false

    ma = metadata(a)
    mb = metadata(b)
    if iscall(a) && iscall(b)
        return isequal_with_metadata(operation(a), operation(b)) && isequal_with_metadata(arguments(a), arguments(b)) && isequal_with_metadata(ma, mb)
    elseif iscall(a) || iscall(b)
        return false
    else
        return isequal_with_metadata(ma, mb)
    end
end

"""
    $(TYPEDSIGNATURES)

Compare the metadata of two `BasicSymbolic`s to ensure it is equal, recursively calling
`isequal_with_metadata` to ensure symbolic variables in the metadata also have equal
metadata.
"""
function isequal_with_metadata(a::NamedTuple, b::NamedTuple)
    a === b && return true
    typeof(a) == typeof(b) || return false

    # same type, so same keys and value types
    # either everything works or it fails and early exits
    for (av, bv) in zip(values(a), values(b))
        isequal_with_metadata(av, bv) || return false
    end

    return true
end

function isequal_with_metadata(a::AbstractDict, b::AbstractDict)
    a === b && return true
    typeof(a) == typeof(b) || return false
    length(a) == length(b) || return false

    # they have same length, so either `b` has all the same keys
    # or this will fail. Can't use `get(b, k, nothing)` because if
    # `a[k] === nothing` it will result in a false positive.
    for (k, v) in a
        k2 = getkey(b, k, nothing)
        isequal_with_metadata(k, k2) || return false
        isequal_with_metadata(v, b[k2]) || return false
    end
    return true
end

function isequal_with_metadata(a::Base.ImmutableDict, b::Base.ImmutableDict)
    a === b && return true
    typeof(a) == typeof(b) || return false
    length(a) == length(b) || return false

    for (k, v) in a
        match = false
        for (k2, v2) in b
            match |= isequal_with_metadata(k, k2) && isequal_with_metadata(v, v2) 
        end
        match || return false
    end
    return true
end

"""
    $(TYPEDSIGNATURES)

Fallback method which uses `isequal`.
"""
isequal_with_metadata(a, b) = isequal(a, b)

"""
    $(TYPEDSIGNATURES)

Specialized methods to check if two ranges are equal without comparing each element.
"""
isequal_with_metadata(a::AbstractRange, b::AbstractRange) = isequal(a, b)

"""
    $(TYPEDSIGNATURES)

Check if two arrays/tuples are equal by calling `isequal_with_metadata` on each element.
This is to ensure true equality of any symbolic elements, if present.
"""
function isequal_with_metadata(a::Union{AbstractArray, Tuple}, b::Union{AbstractArray, Tuple})
    a === b && return true
    typeof(a) == typeof(b) || return false
    if a isa AbstractArray
        size(a) == size(b) || return false
    end # otherwise they're tuples and type equality also checks length equality
    for (x, y) in zip(a, b)
        isequal_with_metadata(x, y) || return false
    end
    return true
end

isequal_with_metadata(a::Number, b::Number) = typeof(a) == typeof(b) && isequal(a, b)

Base.one( s::Symbolic) = one( symtype(s))
Base.zero(s::Symbolic) = zero(symtype(s))

Base.nameof(s::BasicSymbolic) = issym(s) ? s.name : error("None Sym BasicSymbolic doesn't have a name")

## This is much faster than hash of an array of Any
hashvec(xs, z) = foldr(hash, xs, init=z)
hashvec2(xs, z) = foldr(hash2, xs, init=z)
const SYM_SALT = 0x4de7d7c66d41da43 % UInt
const ADD_SALT = 0xaddaddaddaddadda % UInt
const SUB_SALT = 0xaaaaaaaaaaaaaaaa % UInt
const DIV_SALT = 0x334b218e73bbba53 % UInt
const POW_SALT = 0x2b55b97a6efb080c % UInt
function Base.hash(s::BasicSymbolic, salt::UInt)::UInt
    E = exprtype(s)
    if E === SYM
        hash(nameof(s), salt ⊻ SYM_SALT)
    elseif E === ADD || E === MUL
        !iszero(salt) && return hash(hash(s, zero(UInt)), salt)
        h = s.hash[]
        !iszero(h) && return h
        hashoffset = isadd(s) ? ADD_SALT : SUB_SALT
        h′ = hash(hashoffset, hash(s.coeff, hash(s.dict, salt)))
        s.hash[] = h′
        return h′
    elseif E === DIV
        return hash(s.num, hash(s.den, salt ⊻ DIV_SALT))
    elseif E === POW
        hash(s.exp, hash(s.base, salt ⊻ POW_SALT))
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

"""
$(TYPEDSIGNATURES)

Calculates a hash value for a `BasicSymbolic` object, incorporating both its metadata and 
symtype.

This function provides an alternative hashing strategy to `Base.hash` for `BasicSymbolic` 
objects. Unlike `Base.hash`, which only considers the expression structure, `hash2` also 
includes the metadata and symtype in the hash calculation. This can be beneficial for hash 
consing, allowing for more effective deduplication of symbolically equivalent expressions 
with different metadata or symtypes.

Equivalent numbers of different types, such as `0.5::Float64` and 
`(1 // 2)::Rational{Int64}`, have the same default `Base.hash` value. The `hash2` function 
distinguishes these by including their numeric types in the hash calculation to ensure that 
symbolically equivalent expressions with different numeric types are treated as distinct 
objects.
"""
hash2(s, salt::UInt) = hash(s, salt)
function hash2(n::T, salt::UInt) where {T <: Number}
    hash(T, hash(n, salt))
end
hash2(s::BasicSymbolic) = hash2(s, zero(UInt))
function hash2(s::BasicSymbolic{T}, salt::UInt)::UInt where {T}
    E = exprtype(s)
    h::UInt = 0
    if E === SYM
        h = hash(nameof(s), salt ⊻ SYM_SALT)
    elseif E === ADD || E === MUL
        if !iszero(s.hash2[])
            return s.hash2[]
        end 
        hashoffset = isadd(s) ? ADD_SALT : SUB_SALT
        hv = Base.hasha_seed
        for (k, v) in s.dict
            hv ⊻= hash2(k, hash(v))
        end
        h = hash(hv, salt)
        h = hash(hashoffset, hash2(s.coeff, h))
    elseif E === DIV
        h = hash2(s.num, hash2(s.den, salt ⊻ DIV_SALT))
    elseif E === POW
        h = hash2(s.exp, hash2(s.base, salt ⊻ POW_SALT))
    elseif E === TERM
        if !iszero(s.hash2[])
            return s.hash2[]
        end 
        op = operation(s)
        oph = op isa Function ? nameof(op) : op
        h = hashvec2(arguments(s), hash(oph, salt))
    else
        error_on_type()
    end
    h = hash(metadata(s), hash(T, h))
    if hasproperty(s, :hash2)
        s.hash2[] = h
    end
    return h
end

###
### Constructors
###

mutable struct AtomicIDCounter
    @atomic x::UInt64
end

const ID_COUNTER = AtomicIDCounter(0)

"""
$(TYPEDSIGNATURES)

Implements hash consing (flyweight design pattern) for `BasicSymbolic` objects.

This function checks if an equivalent `BasicSymbolic` object already exists. It uses a 
custom hash function (`hash2`) incorporating metadata and symtypes to search for existing 
objects in a `WeakValueDict` (`wvd`). Due to the possibility of hash collisions (where 
different objects produce the same hash), a custom equality check (`isequal_with_metadata`) 
which includes metadata comparison, is used to confirm the equivalence of objects with 
matching hashes. If an equivalent object is found, the existing object is returned; 
otherwise, the input `s` is returned. This reduces memory usage, improves compilation time 
for runtime code generation, and supports built-in common subexpression elimination, 
particularly when working with symbolic objects with metadata.

Using a `WeakValueDict` ensures that only weak references to `BasicSymbolic` objects are 
stored, allowing objects that are no longer strongly referenced to be garbage collected. 
Custom functions `hash2` and `isequal_with_metadata` are used instead of `Base.hash` and 
`Base.isequal` to accommodate metadata without disrupting existing tests reliant on the 
original behavior of those functions.
"""
function BasicSymbolic(s::BasicSymbolic)::BasicSymbolic
    if !ENABLE_HASHCONSING[]
        return s
    end
    cache = wvd[]
    h = hash2(s)
    k = get!(cache, h, s)
    if isequal_with_metadata(k, s)
        if iszero(k.id[])
            k.id[] = @atomic ID_COUNTER.x += 1
        end
        return k
    else
        if iszero(s.id[])
            s.id[] = @atomic ID_COUNTER.x += 1
        end
        return s
    end
end

function Sym{T}(name::Symbol; kw...) where {T}
    s = Sym{T}(; name, kw..., id = Ref{UInt}(0))
    BasicSymbolic(s)
end

function Term{T}(f, args; kw...) where T
    args = SmallV{Any}(args)

    s = Term{T}(;f=f, arguments=args, hash=Ref(UInt(0)), hash2=Ref(UInt(0)), kw..., id = Ref{UInt64}(0))
    BasicSymbolic(s)
end

function Term(f, args; metadata=NO_METADATA)
    Term{_promote_symtype(f, args)}(f, args, metadata=metadata)
end

function unwrap_dict(dict)
    if any(k -> unwrap(k) !== k, keys(dict))
        return typeof(dict)(unwrap(k) => v for (k, v) in dict)
    end
    return dict
end

function Add(::Type{T}, coeff, dict; metadata=NO_METADATA, kw...) where T
    coeff = unwrap(coeff)
    dict = unwrap_dict(dict)
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

    s = Add{T}(; coeff, dict, hash=Ref(UInt(0)), hash2=Ref(UInt(0)), metadata, arguments=SmallV{Any}(), kw..., id = Ref{UInt64}(0))
    BasicSymbolic(s)
end

function Mul(T, a, b; metadata=NO_METADATA, kw...)
    a = unwrap(a)
    b = unwrap_dict(b)
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
        s = Mul{T}(; coeff, dict, hash=Ref(UInt(0)), hash2=Ref(UInt(0)), metadata, arguments=SmallV{Any}(), kw..., id = Ref{UInt64}(0))
        BasicSymbolic(s)
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
            Mul{symtype(x)}(; coeff=x.coeff.num, dict=x.dict, x.metadata, arguments=SmallV{Any}())
        else
            x
        end
    elseif x isa Rational
        isone(x.den) ? x.num : x
    else
        x
    end
end

function Div{T}(n, d, simplified=false; metadata=nothing, kwargs...) where {T}
    n = unwrap(n)
    d = unwrap(d)
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

    s = Div{T}(; num=n, den=d, simplified, arguments=SmallV{Any}(), metadata, id = Ref{UInt64}(0))
    BasicSymbolic(s)
end

function Div(n,d, simplified=false; kw...)
    Div{promote_symtype((/), symtype(n), symtype(d))}(n, d, simplified; kw...)
end

@inline function numerators(x)
    isdiv(x) && return numerators(x.num)
    iscall(x) && operation(x) === (*) ? arguments(x) : Any[x]
end

@inline denominators(x) = isdiv(x) ? numerators(x.den) : Any[1]

function Pow{T}(a, b; metadata=NO_METADATA, kwargs...) where {T}
    a = unwrap(a)
    b = unwrap(b)
    _iszero(b) && return 1
    _isone(b) && return a
    s = Pow{T}(; base=a, exp=b, arguments=SmallV{Any}(), metadata, id = Ref{UInt64}(0))
    BasicSymbolic(s)
end

function Pow(a, b; metadata = NO_METADATA, kwargs...)
    Pow{promote_symtype(^, symtype(a), symtype(b))}(makepow(a, b)...; metadata, kwargs...)
end

function toterm(t::BasicSymbolic{T}) where T
    E = exprtype(t)
    if E === SYM || E === TERM
        return t
    elseif E === ADD || E === MUL
        args = Any[]
        push!(args, t.coeff)
        for (k, coeff) in t.dict
            push!(args, coeff == 1 ? k : Term{T}(E === MUL ? (^) : (*), SmallV{Any}((coeff, k))))
        end
        Term{T}(operation(t), args)
    elseif E === DIV
        Term{T}(/, SmallV{Any}((t.num, t.den)))
    elseif E === POW
        Term{T}(^, SmallV{Any}((t.base, t.exp)))
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
    args = SmallV{Any}(args)
    if type === nothing
        T = _promote_symtype(f, args)
    else
        T = type
    end
    Term{T}(f, args)
end

"""
    unflatten(t::Symbolic{T})
Binarizes `Term`s with n-ary operations
"""
function unflatten(t::Symbolic{T}) where{T}
    if iscall(t)
        f = operation(t)
        if f == (+) || f == (*)   # TODO check out for other n-ary --> binary ops
            a = arguments(t)
            return foldl((x,y) -> Term{T}(f, SmallV{Any}((x, y))), a)
        end
    end
    return t
end

unflatten(t) = t

function TermInterface.maketerm(T::Type{<:BasicSymbolic}, head, args, metadata)
    st = symtype(T)
    pst = _promote_symtype(head, args)
    # Use promoted symtype only if not a subtype of the existing symtype of T.
    # This is useful when calling `maketerm(BasicSymbolic{Number}, (==), [true, false])` 
    # Where the result would have a symtype of Bool. 
    # Please see discussion in https://github.com/JuliaSymbolics/SymbolicUtils.jl/pull/609 
    # TODO this should be optimized.
    new_st = if st <: AbstractArray
        st
    elseif pst === Bool
        pst
    elseif pst === Any || (st === Number && pst <: st)
        st
    else
        pst
    end
    basicsymbolic(head, args, new_st, metadata)
end

function basicsymbolic(f, args, stype, metadata)
    if f isa Symbol
        error("$f must not be a Symbol")
    end
    T = stype
    if T === nothing
        T = _promote_symtype(f, args)
    end
    if T <: LiteralReal
        @goto FALLBACK
    elseif all(x->symtype(x) <: Number, args)
        if f === (+)
            res = +(args...)
            if isadd(res) || (isterm(res) && operation(res) == (+))
                @set! res.metadata = metadata
            end
            res
        elseif f == (*)
            res = *(args...)
            if ismul(res) || (isterm(res) && operation(res) == (*))
                @set! res.metadata = metadata
            end
            res
        elseif f == (/)
            @assert length(args) == 2
            res = args[1] / args[2]
            if isdiv(res)
                @set! res.metadata = metadata
            end
            res
        elseif f == (^) && length(args) == 2
            res = args[1] ^ args[2]
            if ispow(res)
                @set! res.metadata = metadata
            end
            res
        else
            @goto FALLBACK
        end
    else
        @label FALLBACK
        Term{T}(f, args, metadata=metadata)
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

issafecanon(f, s) = true
function issafecanon(f, s::Symbolic)
    if isnothing(metadata(s)) || issym(s)
        return true
    else
        _issafecanon(f, s)
    end
end
_issafecanon(::typeof(*), s) = !iscall(s) || !(operation(s) in (+,*,^))
_issafecanon(::typeof(+), s) = !iscall(s) || !(operation(s) in (+,*))
_issafecanon(::typeof(^), s) = !iscall(s) || !(operation(s) in (*, ^))

issafecanon(f, ss...) = all(x->issafecanon(f, x), ss)

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
    val = unwrap(val)
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
        @set s.metadata = Base.ImmutableDict{DataType, Any}(ctx, unwrap(val))
    end
end


function to_symbolic(x)
    x
end

###
###  Pretty printing
###
const show_simplified = Ref(false)

isnegative(t::Real) = t < 0
function isnegative(t)
    if iscall(t) && operation(t) === (*)
        coeff = first(arguments(t))
        return isnegative(coeff)
    end
    return false
end

# Term{}
setargs(t, args) = Term{symtype(t)}(operation(t), args)
cdrargs(args) = setargs(t, cdr(args))

print_arg(io, x::Union{Complex, Rational}; paren=true) = print(io, "(", x, ")")
isbinop(f) = iscall(f) && !iscall(operation(f)) && Base.isbinaryoperator(nameof(operation(f)))
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
    !iscall(t) && return -t
    @assert operation(t) == (*)
    args = sorted_arguments(t)
    @assert args[1] < 0
    Any[-args[1], args[2:end]...]
end


function show_add(io, args)
    for (i, t) in enumerate(args)
        neg = isnegative(t)
        if i != 1
            print(io, neg ? " - " : " + ")
        elseif isnegative(t)
            print(io, "-")
        end
        if neg
            show_mul(io, remove_minus(t))
        else
            print_arg(io, +, t)
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

    iscall(x) && print(io, "(")
    print(io, x)
    iscall(x) && print(io, ")")
    print(io, "[")
    for i=1:length(idx)
        print_arg(io, idx[i])
        i != length(idx) && print(io, ", ")
    end
    print(io, "]")
end

function show_call(io, f, args)
    fname = iscall(f) ? Symbol(repr(f)) : nameof(f)
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
    args = sorted_arguments(t)
    if symtype(t) <: LiteralReal
        show_call(io, f, args)
    elseif f === (+)
        show_add(io, args)
    elseif f === (*)
        show_mul(io, args)
    elseif f === (^)
        show_pow(io, args)
    elseif f === (getindex)
        show_ref(io, f, args)
    elseif f === (identity) && !issym(args[1]) && !iscall(args[1])
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

struct FnType{X<:Tuple,Y,Z} end

(f::Symbolic{<:FnType})(args...) = Term{promote_symtype(f, symtype.(args)...)}(f, SmallV{Any}(args))

function (f::Symbolic)(args...)
    error("Sym $f is not callable. " *
          "Use @syms $f(var1, var2,...) to create it as a callable.")
end

"""
    promote_symtype(f::FnType{X,Y}, arg_symtypes...)

The output symtype of applying variable `f` to arguments of symtype `arg_symtypes...`.
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
        nt = _name_type(x)
        n, t = nt.name, nt.type
        T = esc(t)
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
            if lhs.args[1] isa Expr
                func_name_and_type = _name_type(lhs.args[1])
                name = func_name_and_type.name
                functype = func_name_and_type.type
            else
                name = lhs.args[1]
                functype = Nothing
            end
            type = map(x->_name_type(x).type, lhs.args[2:end])
            return (name=name, type=:($FnType{Tuple{$(type...)}, $rhs, $functype}))
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

function +(a::SN, bs::SN...)
    isempty(bs) && return a
    # entries where `!issafecanon`
    unsafes = SmallV{Any}()
    # coeff and dict of the `Add`
    coeff = 0
    dict = sdict()
    # type of the `Add`
    T = symtype(a)

    # handle `a` separately
    if issafecanon(+, a)
        if isadd(a)
            coeff = a.coeff
            dict = copy(a.dict)
        elseif ismul(a)
            v = a.coeff
            a′ = Mul(symtype(a), 1, copy(a.dict); metadata = a.metadata)
            dict[a′] = v
        else
            dict[a] = 1
        end
    else
        push!(unsafes, a)
    end

    for b in bs
        T = promote_symtype(+, T, symtype(b))
        if !issafecanon(+, b)
            push!(unsafes, b)
            continue
        end
        if isadd(b)
            coeff += b.coeff
            for (k, v) in b.dict
                dict[k] = get(dict, k, 0) + v
            end
        elseif ismul(b)
            v = b.coeff
            b′ = Mul(symtype(b), 1, copy(b.dict); metadata = b.metadata)
            dict[b′] = get(dict, b′, 0) + v
        else
            dict[b] = get(dict, b, 0) + 1
        end
    end
    # remove entries multiplied by zero
    filter!(dict) do kvp
        !iszero(kvp[2])
    end

    result = isempty(dict) ? coeff : Add(T, coeff, dict)
    if !isempty(unsafes)
        push!(unsafes, result)
        result = Term{T}(+, unsafes)
    end
    return result
end

function +(a::Number, b::SN, bs::SN...)
    b = +(b, bs...)
    issafecanon(+, b) || return term(+, a, b)
    iszero(a) && return b
    if isadd(b)
        Add(add_t(a, b), a + b.coeff, b.dict)
    else
        Add(add_t(a, b), makeadd(1, a, b)...)
    end
end

function +(a::SN, b::Number, bs::SN...)
    return +(b, a, bs...)
end

function -(a::SN)
    !issafecanon(*, a) && return term(-, a)
    isadd(a) ? Add(sub_t(a), -a.coeff, mapvalues((_,v) -> -v, a.dict)) :
    Add(sub_t(a), makeadd(-1, 0, a)...)
end

function -(a::SN, b::SN)
    (!issafecanon(+, a) || !issafecanon(*, b)) && return term(-, a, b)
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
    !issafecanon(*, a, b) && return term(*, a, b)
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
    tmp = unwrap(a)
    if tmp !== a
        return tmp * b
    end
    !issafecanon(*, b) && return term(*, a, b)
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

/(a::SN, b::Number) = (isone(abs(b)) ? b : (b isa Integer ? 1//b : inv(b))) * a

//(a::Union{SN, Number}, b::SN) = a / b

//(a::SN, b::T) where {T <: Number} = (one(T) // b) * a


###
### Pow
###

function ^(a::SN, b)
    b = unwrap(b)
    !issafecanon(^, a,b) && return Pow(a, b)
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
