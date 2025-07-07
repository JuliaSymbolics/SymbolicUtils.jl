#-------------------
#--------------------
#### Symbolic
#--------------------
abstract type Symbolic{T} end

#################### SafeReal #########################
export SafeReal, LiteralReal

# ideally the relationship should be the other way around
abstract type SafeRealImpl <: Number end
const SafeReal = Union{SafeRealImpl, Real}
Base.one(::Type{SafeReal}) = true
Base.zero(::Type{SafeReal}) = false
Base.convert(::Type{<:SafeRealImpl}, x::Number) = convert(Real, x)

################### LiteralReal #######################

abstract type LiteralRealImpl <: Number end
const LiteralReal = Union{LiteralRealImpl, Real}
Base.one(::Type{LiteralReal}) = true
Base.zero(::Type{LiteralReal}) = false
Base.convert(::Type{<:LiteralRealImpl}, x::Number) = convert(Real, x)

###
### Uni-type design
###

struct Unknown end

const MetadataT = Union{Base.ImmutableDict{DataType, Any}, Nothing}
const SmallV{T} = SmallVec{T, Vector{T}}
const ArgsT = SmallV{Any}
const ROArgsT = ReadOnlyVector{Any, ArgsT}
const ACDict{K, V} = Dict{K, V}
const ShapeVecT = SmallV{UnitRange{Int}}
const ShapeT = Union{Unknown, ShapeVecT}
const IdentT = Union{IDType, Nothing}

"""
    Enum used to differentiate between variants of `BasicSymbolicImpl.ACTerm`.
"""
@enumx AddMulVariant::Bool begin
    ADD = false
    MUL = true
end

"""
    $(TYPEDSIGNATURES)

Check if `coeff` is the identity element for `ACTerm` variant `v`.
"""
function is_identity_coeff(v::AddMulVariant.T, coeff)
    @match v begin
        AddMulVariant.ADD => iszero(coeff)
        AddMulVariant.MUL => isone(coeff)
    end
end

"""
    $(TYPEDSIGNATURES)

Get the identity coefficient for `ACTerm` variant `v` as type `T`.
"""
function identity_coeff(v::AddMulVariant.T, T = Bool)
    @match v begin
        AddMulVariant.ADD => zero(T)
        AddMulVariant.MUL => one(T)
    end
end

"""
    $(TYPEDEF)

Core ADT for `BasicSymbolic`. `hash` and `isequal` compare metadata.
"""
@data mutable BasicSymbolicImpl{T} <: Symbolic{T} begin 
    # struct Const{T}
    #     val::T
    #     id::RefValue{IdentT}
    # end
    struct Sym
        const name::Symbol
        const metadata::MetadataT
        const shape::ShapeT
        hash2::UInt
        id::IdentT
    end
    struct Term
        const f::Any
        const args::ArgsT
        const metadata::MetadataT
        const shape::ShapeT
        hash::UInt
        hash2::UInt
        id::IdentT
    end
    struct AddOrMul
        const variant::AddMulVariant.T
        const coeff::T
        const dict::ACDict{Symbolic, T}
        const metadata::MetadataT
        const shape::ShapeT
        const args::ArgsT
        hash::UInt
        hash2::UInt
        id::IdentT
    end
    struct Div
        const num::Any
        const den::Any
        # TODO: Keep or remove?
        # Flag for whether this div is in the most simplified form we can compute.
        # This being false doesn't mean no elimination is performed. Trivials such as
        # constant factors can be eliminated. However, polynomial elimination may not
        # have been performed yet. Typically used as an early-exit for simplification
        # algorithms to not try to eliminate more.
        const simplified::Bool
        const metadata::MetadataT
        const shape::ShapeT
        hash2::UInt
        id::IdentT
    end
    struct Pow
        const base::Any
        const exp::Any
        const metadata::MetadataT
        const shape::ShapeT
        hash2::UInt
        id::IdentT
    end
end

const BSImpl = BasicSymbolicImpl
const BasicSymbolic = BSImpl.Type

function SymbolicIndexingInterface.symbolic_type(::Type{<:BasicSymbolic})
    ScalarSymbolic()
end

function SymbolicIndexingInterface.symbolic_type(::Type{<:BasicSymbolic{<:AbstractArray}})
    ArraySymbolic()
end

"""
    $(TYPEDSIGNATURES)

Return the inner `Symbolic` wrapped in a non-symbolic subtype. Defaults to
returning the input as-is.
"""
unwrap(x) = x

struct UnimplementedForVariantError <: Exception
    method
    variant
end

function Base.showerror(io::IO, err::UnimplementedForVariantError)
    print(io, """
    $(err.method) is not implemented for variant $(err.variant) of `BasicSymbolicImpl`.
    """)
end

"""
    $(TYPEDSIGNATURES)

Properties of `obj` that override any explicitly provided values in
`ConstructionBase.setproperties`.
"""
override_properties(obj::BSImpl.Type) = override_properties(MData.variant_type(obj))

function override_properties(obj::Type{<:BSImpl.Variant})
    @match obj begin
        ::Type{<:BSImpl.Sym} => (; id = nothing, hash2 = 0)
        ::Type{<:BSImpl.Term} => (; id = nothing, hash = 0, hash2 = 0)
        ::Type{<:BSImpl.AddOrMul} => (; id = nothing, hash = 0, hash2 = 0)
        ::Type{<:BSImpl.Div} => (; id = nothing, hash2 = 0)
        ::Type{<:BSImpl.Pow} => (; id = nothing, hash2 = 0)
        _ => throw(UnimplementedForVariantError(override_properties, obj))
    end
end

function ordered_override_properties(obj::Type{<:BSImpl.Variant})
    @match obj begin
        ::Type{<:BSImpl.Sym} => (0, nothing)
        ::Type{<:BSImpl.Term} => (0, 0, nothing)
        ::Type{<:BSImpl.AddOrMul} => (ArgsT(), 0, 0, nothing)
        ::Type{<:BSImpl.Div} => (0, nothing)
        ::Type{<:BSImpl.Pow} => (0, nothing)
        _ => throw(UnimplementedForVariantError(override_properties, obj))
    end
end

function ConstructionBase.getproperties(obj::BSImpl.Type)
    @match obj begin
        BSImpl.Sym(; name, metadata, hash2, shape, id) => (; name, metadata, hash2, shape, id)
        BSImpl.Term(; f, args, metadata, hash, hash2, shape, id) => (; f, args, metadata, hash, hash2, shape, id)
        BSImpl.AddOrMul(; variant, coeff, dict, args, metadata, hash, hash2, shape, id) => (; variant, coeff, dict, args, metadata, hash, hash2, shape, id)
        BSImpl.Div(; num, den, simplified, metadata, hash2, shape, id) => (; num, den, simplified, metadata, hash2, shape, id)
        BSImpl.Pow(; base, exp, metadata, hash2, shape, id) => (; base, exp, metadata, hash2, shape, id)
    end
end

function ConstructionBase.setproperties(obj::BSImpl.Type{T}, patch::NamedTuple)::BSImpl.Type{T} where {T}
    props = getproperties(obj)
    overrides = override_properties(obj)
    # We only want to invalidate `args` if we're updating `coeff` or `dict`.
    if isaddmul(obj) && (haskey(patch, :coeff) || haskey(patch, :dict))
        extras = (; args = ArgsT())
    else
        extras = (;)
    end
    hashcons(MData.variant_type(obj)(; props..., patch..., overrides..., extras...))
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
@inline symtype(::BSImpl.Type{T}) where T = T
@inline symtype(::Type{<:BSImpl.Type{T}}) where T = T

"""
    operation(expr)

Extract the operation (function) from a symbolic function call expression.
Only valid for expressions where `iscall(expr)` returns `true`.

Returns the function/operator that is being applied in the expression. For basic
arithmetic, this returns the operator function (+, -, *, /, ^). For function calls
like `sin(x)`, this returns the function `sin`.

# Examples
```julia
using SymbolicUtils
@variables x y

# Arithmetic operations
expr1 = x + y
operation(expr1)    # returns +

expr2 = x * y  
operation(expr2)    # returns *

# Function calls
expr3 = sin(x)
operation(expr3)    # returns sin

# Nested expressions
expr4 = sin(x + y)
operation(expr4)    # returns sin
operation(arguments(expr4)[1])  # returns +
```

See also: [`iscall`](@ref), [`arguments`](@ref)
"""
# We're returning a function pointer
@inline function TermInterface.operation(x::BSImpl.Type)
    @match x begin
        # BSImpl.Const(_) => throw(ArgumentError("`Const` does not have an operation."))
        BSImpl.Sym(_) => throw(ArgumentError("`Sym` does not have an operation."))
        BSImpl.Term(; f) => f
        BSImpl.AddOrMul(; variant) => @match variant begin
                AddMulVariant.ADD => (+)
                AddMulVariant.MUL => (*)
            end
        BSImpl.Div(_) => (/)
        BSImpl.Pow(_) => (^)
        _ => throw(UnimplementedForVariantError(operation, MData.variant_type(x)))
    end
end

"""
    sorted_arguments(x::BasicSymbolic)

Get the arguments of a symbolic expression in canonical sorted order.

For commutative operations like addition and multiplication, the arguments
are sorted according to a canonical ordering. This ensures that equivalent
expressions have the same representation.

# Arguments
- `x::BasicSymbolic`: The symbolic expression

# Returns
A vector of the arguments in sorted order. For non-commutative operations,
returns the arguments in their original order.

# Examples
```julia
julia> @syms x y z
(x, y, z)

julia> expr = x + z + y
x + y + z

julia> sorted_arguments(expr)
3-element Vector{Any}:
 x
 y
 z
```
"""
@cache function TermInterface.sorted_arguments(x::BSImpl.Type)::ROArgsT
    @match x begin
        BSImpl.AddOrMul(; variant) => begin
                args = copy(parent(arguments(x)))
                @match variant begin
                    AddMulVariant.ADD => sort!(args, by = get_degrees, lt = monomial_lt)
                    AddMulVariant.MUL => sort!(args, by = get_degrees)
                end
                return ROArgsT(ArgsT(args))
            end
        _ => return arguments(x)
    end
end

"""
    arguments(expr)

Extract the arguments from a symbolic function call expression.
Only valid for expressions where `iscall(expr)` returns `true`.

Returns a collection (typically a vector) containing the arguments passed to the operation.
For binary operations like `+` or `*`, this returns a collection of all operands.
For function calls, this returns the function arguments.

# Examples
```julia
using SymbolicUtils
@variables x y z

# Binary arithmetic operations
expr1 = x + y
arguments(expr1)    # returns collection containing x and y

expr2 = x * y * z  
arguments(expr2)    # returns collection containing x, y, and z

# Function calls
expr3 = sin(x)
arguments(expr3)    # returns collection containing x

# Nested expressions
expr4 = sin(x + y)
arguments(expr4)             # returns collection containing (x + y)
arguments(arguments(expr4)[1])  # returns collection containing x and y
```

See also: [`iscall`](@ref), [`operation`](@ref)
"""
function TermInterface.arguments(x::BSImpl.Type)::ROArgsT
    @match x begin
        # BSImpl.Const(_) => throw(ArgumentError("`Const` does not have arguments."))
        BSImpl.Sym(_) => throw(ArgumentError("`Sym` does not have arguments."))
        BSImpl.Term(; args) => ROArgsT(args)
        BSImpl.AddOrMul(; args, coeff, dict, variant) => begin
                isempty(args) || return ROArgsT(args)
                sz = length(dict)
                idcoeff = is_identity_coeff(variant, coeff)
                sizehint!(args, sz + !idcoeff)
                idcoeff || push!(args, coeff)
                @match variant begin
                    AddMulVariant.ADD => begin
                        for (k, v) in dict
                            var = if isone(v)
                                k
                            elseif applicable(*, k, v)
                                k * v
                            else
                                maketerm(k, *, [k, v], nothing)
                            end
                            push!(args, var)
                        end
                    end
                    AddMulVariant.MUL => begin
                        for (k, v) in dict
                            push!(args, isone(v) ? k : (k ^ v))
                        end
                    end
                end
                return ROArgsT(args)
            end
        BSImpl.Div(num, den) => ROArgsT(ArgsT((num, den)))
        BSImpl.Pow(base, exp) => ROArgsT(ArgsT((base, exp)))
        _ => throw(UnimplementedForVariantError(arguments, MData.variant_type(x)))
    end
end

function isexpr(s::BSImpl.Type)
    !MData.isa_variant(s, BSImpl.Sym) # && !MData.isa_variant(s.inner, BSImpl.Const)
end

"""
    iscall(expr)

Check if a symbolic expression `expr` represents a function call. Returns `true` if the 
expression is a composite expression with an operation and arguments, `false` otherwise.

This function is fundamental for traversing and analyzing symbolic expressions. In 
SymbolicUtils.jl, an expression is considered a "call" if it represents a function 
application (including operators like +, -, *, etc.).

# Examples
```julia
using SymbolicUtils
@variables x y

# Basic variables are not calls
iscall(x)           # false

# Function calls are calls  
expr = sin(x + y)
iscall(expr)        # true

# Arithmetic expressions are calls
iscall(x + y)       # true
iscall(x * y)       # true
```

See also: [`operation`](@ref), [`arguments`](@ref)
"""
iscall(s::BSImpl.Type) = isexpr(s)

# isconst(x::BSImpl.Type) = MData.isa_variant(x, BSImpl.Const)
isconst(x) = false
issym(x::BSImpl.Type) = MData.isa_variant(x, BSImpl.Sym)
isterm(x::BSImpl.Type) = MData.isa_variant(x, BSImpl.Term)
isaddmul(x::BSImpl.Type) = MData.isa_variant(x, BSImpl.AddOrMul)
isadd(x::BSImpl.Type) = MData.isa_variant(x, BSImpl.AddOrMul) && x.variant == AddMulVariant.ADD
ismul(x::BSImpl.Type) = MData.isa_variant(x, BSImpl.AddOrMul) && x.variant == AddMulVariant.MUL
isdiv(x::BSImpl.Type) = MData.isa_variant(x, BSImpl.Div)
ispow(x::BSImpl.Type) = MData.isa_variant(x, BSImpl.Pow)

for fname in [:issym, :isterm, :isaddmul, :isadd, :ismul, :isdiv, :ispow]
    @eval $fname(x) = false
end

###
### Base interface
###

Base.isequal(::Symbolic, x) = false
Base.isequal(x, ::Symbolic) = false
Base.isequal(::Symbolic, ::Missing) = false
Base.isequal(::Missing, ::Symbolic) = false
Base.isequal(::Symbolic, ::Symbolic) = false

Base.@nospecializeinfer function isequal_maybe_scal(a, b, full::Bool)
    @nospecialize a b
    if a isa BasicSymbolic{Number} && b isa BasicSymbolic{Number}
        isequal_bsimpl(a, b, full)
    elseif a isa Int && b isa Int
        isequal(a, b)
    elseif a isa Float64 && b isa Float64
        isequal(a, b)
    elseif a isa Rational{Int} && b isa Rational{Int}
        isequal(a, b)
    else
        isequal(a, b)::Bool
    end
end

const COMPARE_FULL = TaskLocalValue{Bool}(Returns(false))

macro manually_scope(val, expr, is_forced = false)
    @assert Meta.isexpr(val, :call)
    @assert val.args[1] == :(=>)

    var_name = val.args[2]
    new_val = val.args[3]
    old_name = gensym(:old_val)
    cur_name = gensym(:cur_val)
    retval_name = gensym(:retval)
    close_expr = :($var_name[] = $old_name)
    interpolated_expr = MacroTools.postwalk(expr) do ex
        if Meta.isexpr(ex, :return)
            return Expr(:block, close_expr, ex)
        elseif Meta.isexpr(ex, :$) && length(ex.args) == 1 && ex.args[1] == :$
            return cur_name
        else
            return ex
        end
    end
    basic_result = quote
        $cur_name = $var_name[] = $new_val
        $retval_name = begin
            $interpolated_expr
        end
        $close_expr
        $retval_name
    end
    is_forced && return quote
        $old_name = $var_name[]
        $basic_result
    end |> esc

    return quote
        $old_name = $var_name[]
        if $iszero($old_name)
            $basic_result
        else
            $cur_name = $old_name
            $retval_name = begin
                $interpolated_expr
            end
        end
        $retval_name
    end |> esc
end

function isequal_symdict(a::Dict, b::Dict, full)
    full || return isequal(a, b)
    length(a) == length(b) || return false
    for (k, v) in a
        k2 = nothing
        v2 = nothing
        @manually_scope COMPARE_FULL => false begin
            k2 = getkey(b, k, nothing)
            k2 === nothing && return false
            v2 = b[k2]
        end true
        v == v2 && isequal_bsimpl(k, k2, true) || return false
    end
    return true
end

function isequal_bsimpl(a::BSImpl.Type, b::BSImpl.Type, full)
    a === b && return true
    ida = a.id
    idb = b.id
    ida === idb && ida !== nothing && return true
    typeof(a) === typeof(b) || return false

    Ta = MData.variant_type(a)
    Tb = MData.variant_type(b)
    Ta === Tb || return false


    if full && ida !== idb && ida !== nothing && idb !== nothing
        return false
    end

    partial = @match (a, b) begin
        (BSImpl.Sym(; name = n1, shape = s1), BSImpl.Sym(; name = n2, shape = s2)) => begin
            n1 === n2 && s1 == s2
        end
        (BSImpl.Term(; f = f1, args = args1, shape = s1), BSImpl.Term(; f = f2, args = args2, shape = s2)) => begin
            isequal(f1, f2)::Bool && isequal(args1, args2) && s1 == s2
        end
        (BSImpl.AddOrMul(; variant = v1, dict = d1, coeff = c1), BSImpl.AddOrMul(; variant = v2, dict = d2, coeff = c2)) => begin
            v1 == v2 && isequal_symdict(d1, d2, full) && isequal_maybe_scal(c1, c2, full)
        end
        (BSImpl.Div(; num = n1, den = d1), BSImpl.Div(; num = n2, den = d2)) => begin
            isequal_maybe_scal(n1, n2, full) && isequal_maybe_scal(d1, d2, full)
        end
        (BSImpl.Pow(; base = n1, exp = d1), BSImpl.Pow(; base = n2, exp = d2)) => begin
            isequal_maybe_scal(n1, n2, full) && isequal_maybe_scal(d1, d2, full)
        end
    end
    if full && partial
        partial = isequal(metadata(a), metadata(b))
    end
    return partial
end

function Base.isequal(a::BSImpl.Type, b::BSImpl.Type)
    isequal_bsimpl(a, b, COMPARE_FULL[])
end

# const CONST_SALT = 0x194813feb8a8c83d % UInt
const SYM_SALT = 0x4de7d7c66d41da43 % UInt
const ADD_SALT = 0xaddaddaddaddadda % UInt
const MUL_SALT = 0xaaaaaaaaaaaaaaaa % UInt
const DIV_SALT = 0x334b218e73bbba53 % UInt
const POW_SALT = 0x2b55b97a6efb080c % UInt

const SCALAR_SYMTYPE_VARIANTS = [Number, Real, SafeReal, LiteralReal]
const ARR_VARIANTS = [Vector, Matrix]
const SYMTYPE_VARIANTS = [SCALAR_SYMTYPE_VARIANTS; [A{T} for A in ARR_VARIANTS for T in SCALAR_SYMTYPE_VARIANTS]]

Base.@nospecializeinfer function hash_coeff(x::Number, h::UInt)
    @nospecialize x
    if x isa Int
        hash(x, h)
    elseif x isa Float64
        hash(x, h)
    elseif x isa Rational{Int}
        hash(x, h)
    elseif x isa UInt
        hash(x, h)
    elseif x isa Bool
        hash(x, h)
    else
        hash(x, h)::UInt
    end
end

Base.@nospecializeinfer function hash_anyscalar(x::Any, h::UInt, full::Bool)
    @nospecialize x
    if x isa Int
        hash(x, h)
    elseif x isa Float64
        hash(x, h)
    elseif x isa Rational{Int}
        hash(x, h)
    elseif x isa UInt
        hash(x, h)
    elseif x isa Bool
        hash(x, h)
    elseif x isa BasicSymbolic{Number}
        hash_bsimpl(x, h, full)
    else
        hash(x, h)::UInt
    end
end

function custom_dicthash(x::Dict{Symbolic, Number}, h::UInt, full)
    hv = Base.hasha_seed
    for (k, v) in x
        h1 = hash_anyscalar(v, zero(UInt), full)
        h1 = hash_anyscalar(k, h1, full)
        hv ⊻= h1
    end
    return hash(hv, h)
end

Base.@nospecializeinfer function hash_addmuldict(x::Dict, h::UInt, full)
    @nospecialize x
    if x isa Dict{Symbolic, Number}
        custom_dicthash(x, h, full)
    else
        hash(x, h)::UInt
    end
end

function hashargs(x::ArgsT, h::UInt, full)
    h += Base.hash_abstractarray_seed
    h = hash(length(x), h)
    for val in x
        h = hash_anyscalar(val, h, full)
    end
    return h
end

function hash_bsimpl(s::BSImpl.Type, h::UInt, full)
    if full
        cache = s.hash2
        !iszero(cache) && return cache
    end
    
    partial::UInt = @match s begin
        BSImpl.Sym(; name, shape) => begin
            h = Base.hash(name, h)
            h = Base.hash(shape, h)
            h ⊻ SYM_SALT
        end
        BSImpl.Term(; f, args, shape, hash) => begin
            # use/update cached hash
            # error()
            cache = hash
            if iszero(cache)
                s.hash = Base.hash(f, hashargs(args, Base.hash(shape, h), full))::UInt
            else
                cache
            end
        end
        BSImpl.AddOrMul(; variant, dict, coeff, shape, hash) => begin
            cache = hash
            if iszero(cache)
                inner = hash_addmuldict(dict, h, full)
                inner = Base.hash(shape, hash_coeff(coeff, inner))
                inner = Base.hash((variant == AddMulVariant.ADD ? ADD_SALT : MUL_SALT), inner)
                s.hash = inner
            else
                cache
            end
            
        end
        BSImpl.Div(; num, den) => begin
            hash_anyscalar(num, hash_anyscalar(den, h, full), full) ⊻ DIV_SALT
        end
        BSImpl.Pow(; base, exp) => begin
            hash_anyscalar(base, hash_anyscalar(exp, h, full), full) ⊻ POW_SALT
        end
    end

    if full
        partial = s.hash2 = Base.hash(metadata(s), partial)::UInt
    end
    return partial
end

function Base.hash(s::BSImpl.Type, h::UInt)
    if !iszero(h)
        return hash(hash(s, zero(h)), h)::UInt
    end
    hash_bsimpl(s, h, COMPARE_FULL[])
end

Base.one( s::Union{Symbolic, BSImpl.Type}) = one( symtype(s))
Base.zero(s::Union{Symbolic, BSImpl.Type}) = zero(symtype(s))


Base.nameof(s::Union{BasicSymbolic, BSImpl.Type}) = issym(s) ? s.name : error("Non-Sym BasicSymbolic doesn't have a name")

###
### Constructors
###

const ENABLE_HASHCONSING = Ref(true)
# const WKD = TaskLocalValue{WeakKeyDict{HashconsingWrapper, Nothing}}(WeakKeyDict{HashconsingWrapper, Nothing})
const WKD = TaskLocalValue{WeakKeyDict{BSImpl.Type, Nothing}}(WeakKeyDict{BSImpl.Type, Nothing})
const WVD = TaskLocalValue{WeakValueDict{UInt, BSImpl.Type}}(WeakValueDict{UInt, BSImpl.Type})
const WCS = TaskLocalValue{WeakCacheSet{BSImpl.Type}}(WeakCacheSet{BSImpl.Type})

function generate_id()
    return IDType()
end

const TOTAL = TaskLocalValue{Int}(Returns(0))
const HITS = TaskLocalValue{Int}(Returns(0))
const MISSES = TaskLocalValue{Int}(Returns(0))
const COLLISIONS = TaskLocalValue{Int}(Returns(0))

"""
$(TYPEDSIGNATURES)

Implements hash consing (flyweight design pattern) for `BasicSymbolic` objects.

This function checks if an equivalent `BasicSymbolic` object already exists. It uses a 
custom hash function (`hash2`) incorporating metadata and symtypes to search for existing 
objects in a `WeakCacheSet` (`wcs`). Due to the possibility of hash collisions (where 
different objects produce the same hash), a custom equality check (`isequal_with_metadata`) 
which includes metadata comparison, is used to confirm the equivalence of objects with 
matching hashes. If an equivalent object is found, the existing object is returned; 
otherwise, the input `s` is returned. This reduces memory usage, improves compilation time 
for runtime code generation, and supports built-in common subexpression elimination, 
particularly when working with symbolic objects with metadata.

Using a `WeakCacheSet` ensures that only weak references to `BasicSymbolic` objects are 
stored, allowing objects that are no longer strongly referenced to be garbage collected. 
Custom functions `hash2` and `isequal_with_metadata` are used instead of `Base.hash` and 
`Base.isequal` to accommodate metadata without disrupting existing tests reliant on the 
original behavior of those functions.
"""

const collides = TaskLocalValue{Any}(Returns(Dict()))

function hashcons(s::BSImpl.Type{T})::BSImpl.Type{T} where {T}
    if !ENABLE_HASHCONSING[]
        return s
    end
    @manually_scope COMPARE_FULL => true begin
        cache = WCS[]
        k = getkey!(cache, s)
        # cache = WVD[]
        # h = hash(s)
        # k = get(cache, h, nothing)

        # if k === nothing || !isequal(k, s)
        #     if k !== nothing
        #         buffer = collides[]
        #         buffer2 = get!(() -> [], buffer, h)
        #         push!(buffer2, k => s)
        #     end
        
        #     cache[h] = s
        #     k = s
        # end
        if k.id === nothing
            k.id = generate_id()
        end
        return k
    end true
end

# function BSImpl.Const{T}(val::T) where {T}
#     hashcons(BSImpl.Const{T}(; val, override_properties(BSImpl.Const{T})...))
# end

parse_metadata(x::MetadataT) = x
parse_metadata(::Nothing) = nothing
function parse_metadata(x)
    meta = MetadataT()
    for kvp in x
        meta = Base.ImmutableDict(meta, kvp)
    end
    return meta
end

default_shape(::Type{<:AbstractArray}) = Unknown()
default_shape(_) = ShapeVecT()

"""
    $(METHODLIST)

If `x` is a rational with denominator 1, turn it into an integer.
"""
function maybe_integer(x)
    x = unwrap(x)
    x isa Real || return x
    isinteger(x) || return x
    if typemin(Int) <= x <= typemax(Int)
        return Int(x)
    else
        return x
    end
end

function parse_args(args::AbstractVector)
    if args isa ROArgsT
        args = parent(args)
    elseif !(args isa ArgsT)
        args = ArgsT(args)
    end
    return args::ArgsT
end

function parse_dict(::Type{T}, x::AbstractDict) where {T}
    if !(x isa ACDict{Symbolic, T})
        x = ACDict{Symbolic, T}(x)
    end
    map!(maybe_integer, values(x))
    return x::ACDict{Symbolic, T}
end

parse_maybe_symbolic(x::Symbolic) = x
parse_maybe_symbolic(x) = x
# parse_maybe_symbolic(x) = Const{typeof(x)}(x)

function unwrap_args(args)
    if any(x -> unwrap(x) !== x, args)
        map(unwrap, args)
    else
        args
    end
end

function unwrap_dict(dict)
    if any(k -> unwrap(k) !== k, keys(dict))
        return typeof(dict)(unwrap(k) => v for (k, v) in dict)
    end
    return dict
end

@inline function BSImpl.Sym{T}(name::Symbol; metadata = nothing, shape = default_shape(T), unsafe = false) where {T}
    metadata = parse_metadata(metadata)
    props = ordered_override_properties(BSImpl.Sym)
    var = BSImpl.Sym{T}(name, metadata, shape, props...)
    if !unsafe
        var = hashcons(var)
    end
    return var
end

@inline function BSImpl.Term{T}(f, args; metadata = nothing, shape = default_shape(T), unsafe = false) where {T}
    metadata = parse_metadata(metadata)
    args = parse_args(args)
    props = ordered_override_properties(BSImpl.Term)
    var = BSImpl.Term{T}(f, args, metadata, shape, props...)
    if !unsafe
        var = hashcons(var)
    end
    return var
end

@inline function BSImpl.AddOrMul{T}(variant::AddMulVariant.T, coeff::T, dict::AbstractDict; metadata = nothing, shape = default_shape(T), unsafe = false) where {T}
    metadata = parse_metadata(metadata)
    dict = parse_dict(T, dict)
    props = ordered_override_properties(BSImpl.AddOrMul)
    coeff = maybe_integer(coeff)
    var = BSImpl.AddOrMul{T}(variant, coeff, dict, metadata, shape, props...)
    if !unsafe
        var = hashcons(var)
    end
    return var
end

@inline function BSImpl.Div{T}(num, den, simplified::Bool; metadata = nothing, shape = default_shape(T), unsafe = false) where {T}
    metadata = parse_metadata(metadata)
    num = maybe_integer(parse_maybe_symbolic(num))
    den = maybe_integer(parse_maybe_symbolic(den))
    props = ordered_override_properties(BSImpl.Div)
    var = BSImpl.Div{T}(num, den, simplified, metadata, shape, props...)
    if !unsafe
        var = hashcons(var)
    end
    return var
end

@inline function BSImpl.Pow{T}(base, exp; metadata = nothing, shape = default_shape(T), unsafe = false) where {T}
    metadata = parse_metadata(metadata)
    base = maybe_integer(parse_maybe_symbolic(base))
    exp = maybe_integer(parse_maybe_symbolic(exp))
    props = ordered_override_properties(BSImpl.Pow)
    var = BSImpl.Pow{T}(base, exp, metadata, shape, props...)
    if !unsafe
        var = hashcons(var)
    end
    return var
end

# struct Const{T} end
struct Sym{T} end
struct Term{T} end
struct Add{T} end
struct Mul{T} end
struct Div{T} end
struct Pow{T} end

# function Const{T}(val)::Symbolic where {T}
#     val = unwrap(val)
#     val isa Symbolic && return val
#     BasicSymbolic(BSImpl.Const{T}(convert(T, val)))
# end

# Const(val) = Const{typeof(val)}(val)

Sym{T}(name; kw...) where {T} = BSImpl.Sym{T}(name; kw...)

function Term{T}(f, args; kw...) where {T}
    args = unwrap_args(args)
    BSImpl.Term{T}(f, args; kw...)
end

function Term(f, args; kw...)
    Term{_promote_symtype(f, args)}(f, args; kw...)
end

# assumes associative commutative addition
function Add{T}(coeff, dict; kw...) where {T}
    coeff = convert(T, maybe_integer(unwrap(coeff)))
    dict = unwrap_dict(dict)
    isempty(dict) && return coeff
    if _iszero(coeff) && length(dict) == 1
        k, v = first(dict)
        _isone(v) && return k
        return k * v
    end

    variant = AddMulVariant.ADD
    BSImpl.AddOrMul{T}(variant, coeff, dict; kw...)
end

function Mul{T}(coeff, dict; kw...) where {T}
    coeff = convert(T, maybe_integer(unwrap(coeff)))
    dict = unwrap_dict(dict)
    isempty(dict) && return coeff
    if _isone(coeff) && length(dict) == 1
        k, v = first(dict)
        _isone(v) && return k
        return k ^ v
    end

    variant = AddMulVariant.MUL
    BSImpl.AddOrMul{T}(variant, coeff, dict; kw...)
end

"""
    $(TYPEDSIGNATURES)

Create a generic division term. Does not assume anything about the division algebra beyond
the ability to check for zero and one elements (via [`_iszero`](@ref) and [`_isone`](@ref)).

If the numerator is zero or denominator is one, the numerator is returned.
"""
function Div{T}(n, d, simplified; kw...) where {T}
    n = unwrap(n)
    d = unwrap(d)
    # TODO: This used to return `zero(typeof(n))`, maybe there was a reason?
    _iszero(n) && return n
    _isone(d) && return n
    return BSImpl.Div{T}(n, d, simplified; kw...)
end

const Rat = Union{Rational, Integer}

"""
    $(TYPEDSIGNATURES)

Return a tuple containing a boolean indicating whether `x` has a rational/integer factor
and the rational/integer factor (or `NaN` otherwise).
"""
function ratcoeff(x)
    if ismul(x)
        ratcoeff(x.coeff)
    elseif x isa Rat
        (true, x)
    else
        (false, NaN)
    end
end

"""
    $(TYPEDSIGNATURES)

Simplify the coefficients of `n` and `d` (numerator and denominator).
"""
function simplify_coefficients(n, d)
    nrat, nc = ratcoeff(n)
    drat, dc = ratcoeff(d)
    nrat && drat || return n, d
    g = gcd(nc, dc) * sign(dc) # make denominator positive
    invdc = isone(g) ? g : (1 // g)
    n = maybe_integer(invdc * n)
    d = maybe_integer(invdc * d)

    return n, d
end

"""
    $(TYPEDSIGNATURES)

Create a division term specifically for the real or complex algebra. Performs additional
simplification and cancellation.
"""
function Div{T}(n, d, simplified; kw...) where {T <: Number}
    n = unwrap(n)
    d = unwrap(d)

    if !(T == SafeReal)
        n, d = quick_cancel(n, d)
    end

    _iszero(n) && return zero(typeof(n))
    _isone(d) && return n

    if isdiv(n) && isdiv(d)
        return Div{T}(n.num * d.den, n.den * d.num, simplified; kw...)
    elseif isdiv(n)
        return Div{T}(n.num, n.den * d, simplified; kw...)
    elseif isdiv(d)
        return Div{T}(n * d.den, d.num, simplified; kw...)
    end

    d isa Number && _isone(-d) && return -n
    n isa Rat && d isa Rat && return n // d

    n, d = simplify_coefficients(n, d)

    _isone(d) && return n
    _isone(-d) && return -n

    BSImpl.Div{T}(n, d, simplified; kw...)
end

function Div(n, d, simplified; kw...)
    Div{promote_symtype((/), symtype(n), symtype(d))}(n, d, simplified; kw...)
end

"""
    $(TYPEDSIGNATURES)

Return the numerator of expression `x` as an array of multiplied terms.
"""
@inline function numerators(x)
    isdiv(x) && return numerators(x.num)
    iscall(x) && operation(x) === (*) && return arguments(x)
    return SmallV{Any}((x,))
end

"""
    $(TYPEDSIGNATURES)

Return the denominator of expression `x` as an array of multiplied terms.
"""
@inline denominators(x) = isdiv(x) ? numerators(x.den) : SmallV{Any}((1,))

function Pow{T}(base, exp; kw...) where {T}
    base = unwrap(base)
    exp = unwrap(exp)
    # TODO: Returning 1 isn't valid for matrix algebra
    # This should use a `_one` function
    _iszero(exp) && return 1
    _isone(exp) && return base
    return BSImpl.Pow{T}(base, exp; kw...)
end

function Pow(a, b; kw...)
    Pow{promote_symtype(^, symtype(a), symtype(b))}(makepow(a, b)...; kw...)
end

function _mergedict!(dict::AbstractDict, other::AbstractDict)
    for (k, v) in other
        vv = get(dict, k, 0)
        dict[k] = v + vv
    end
end

function unwrap_const(x)
    x
    # isconst(x) ? x.val : x
end

"""
    $(TYPEDSIGNATURES)

Return the `coeff` and `dict` for adding `xs...` into a symbolic of symtype `T`.
"""
function makeadd(::Type{T}, xs...)::Tuple{T, Dict{Symbolic, T}} where {T}
    dict = Dict{Symbolic, T}()
    coeff = zero(T)

    for x in xs
        x = unwrap_const(unwrap(x))
        if x isa Number
            coeff += convert(T, x)
            continue
        elseif isadd(x)
            coeff += x.coeff
            _mergedict!(dict, x.dict)
            continue
        end
        if ismul(x)
            v = x.coeff
            k = Mul{T}(1, x.dict; metadata = metadata(x))
        else
            k = x
            v = 1
        end
        dict[k] = get(dict, k, zero(T)) + v
    end
    filter!(!iszero ∘ last, dict)
    return coeff, dict
end

"""
    $(TYPEDSIGNATURES)

Return the `coeff` and `dict` for multiplying `xs...` into a symbolic of symtype `T`.
"""
function makemul(::Type{T}, xs...) where {T}
    dict = Dict{Symbolic, T}()
    coeff = one(T)
    for x in xs
        x = unwrap_const(unwrap(x))
        if ispow(x) && x.exp isa T
        # if ispow(x) && isconst(x.exp)
            dict[x.base] = x.exp + get(dict, x.base, 0)
        elseif x isa Number
            coeff *= convert(T, x)
        elseif ismul(x)
            coeff *= x.coeff
            _mergedict!(dict, x.dict)
        else
            dict[x] = get(dict, x, 0) + 1
        end
    end

    filter!(!iszero ∘ last, dict)
    return (coeff, dict)
end

"""
    $(TYPEDSIGNATURES)

Return the base and exponent for representing `a^b`.
"""
function makepow(a, b)
    a = unwrap(a)
    b = unwrap(b)
    base = a
    exp = b
    if ispow(a)
        base = a.base
        exp = a.exp * b
    end
    return (base, exp)
end

"""
    term(f, args...; type = nothing)

Create a symbolic term with operation `f` and arguments `args`.

# Arguments
- `f`: The operation or function head of the term
- `args...`: The arguments to the operation
- `type`: Optional type specification for the term. If not provided, the type is inferred using `promote_symtype`.

# Examples
```julia
julia> @syms x y
(x, y)

julia> term(+, x, y)
x + y

julia> term(sin, x)
sin(x)

julia> term(^, x, 2)
x^2
```
"""
function term(f, args...; type = nothing)
    args = SmallV{Any}(args)
    if type === nothing
        T = _promote_symtype(f, args)
    else
        T = type
    end
    Term{T}(f, args)
end

function TermInterface.maketerm(T::Type{<:BasicSymbolic}, head, args, metadata)
    args = unwrap_args(args)
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
    args = unwrap_args(args)
    T = stype
    if T === nothing
        T = _promote_symtype(f, args)
    end
    if T == LiteralReal
        @goto FALLBACK
    elseif all(x->symtype(x) <: Number, args)
        if f === (+)
            res = add_worker(args)
            if metadata !== nothing && (isadd(res) || (isterm(res) && operation(res) == (+)))
                @set! res.metadata = metadata
            end
            res
        elseif f == (*)
            res = mul_worker(args)
            if metadata !== nothing && (ismul(res) || (isterm(res) && operation(res) == (*)))
                @set! res.metadata = metadata
            end
            res
        elseif f == (/)
            @assert length(args) == 2
            res = args[1] / args[2]
            if metadata !== nothing && isdiv(res)
                @set! res.metadata = metadata
            end
            res
        elseif f == (^) && length(args) == 2
            res = args[1] ^ args[2]
            if metadata !== nothing && ispow(res)
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
metadata(s::BSImpl.Type) = s.metadata
# metadata(s::HashconsingWrapper) = throw(MethodError(metadata, (s,)))
metadata(s::Symbolic) = s.metadata
metadata(s::Symbolic, meta) = Setfield.@set! s.metadata = meta

"""
    hasmetadata(s::Symbolic, ctx)

Check if a symbolic expression has metadata for a given context.

# Arguments
- `s::Symbolic`: The symbolic expression to check
- `ctx`: The metadata context key (typically a DataType)

# Returns
- `true` if the expression has metadata for the given context, `false` otherwise

# Examples
```julia
julia> @syms x
x

julia> hasmetadata(x, Float64)
false
```
"""
function hasmetadata(s::Symbolic, ctx)
    metadata(s) isa AbstractDict && haskey(metadata(s), ctx)
end

issafecanon(f, s) = true
function issafecanon(f, s::Symbolic)
    if metadata(s) === nothing || isempty(metadata(s)) || issym(s)
        return true
    else
        _issafecanon(f, s)
    end
end
_issafecanon(::typeof(*), s) = !iscall(s) || !(operation(s) in (+,*,^))
_issafecanon(::typeof(+), s) = !iscall(s) || !(operation(s) in (+,*))
_issafecanon(::typeof(^), s) = !iscall(s) || !(operation(s) in (*, ^))

issafecanon(f, ss...) = all(x->issafecanon(f, x), ss)

"""
    getmetadata(s::Symbolic, ctx)

Retrieve metadata associated with a symbolic expression for a given context.

# Arguments
- `s::Symbolic`: The symbolic expression
- `ctx`: The metadata context key (typically a DataType)

# Returns
The metadata value associated with the given context

# Throws
- `ArgumentError` if the expression does not have metadata for the given context

# Examples
```julia
julia> @syms x::Float64
x

julia> getmetadata(x, symtype)  # Get the type metadata
Float64
```
"""
function getmetadata(s::Symbolic, ctx)
    md = metadata(s)
    if md isa AbstractDict
        md[ctx]
    else
        throw(ArgumentError("$s does not have metadata for $ctx"))
    end
end

"""
    getmetadata(s::Symbolic, ctx, default)

Retrieve metadata associated with a symbolic expression for a given context,
returning a default value if not found.

# Arguments
- `s::Symbolic`: The symbolic expression
- `ctx`: The metadata context key (typically a DataType)
- `default`: The default value to return if metadata is not found

# Returns
The metadata value associated with the given context, or `default` if not found

# Examples
```julia
julia> @syms x
x

julia> getmetadata(x, Float64, "no type")
"no type"
```
"""
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

"""
    setmetadata(s::Symbolic, ctx::DataType, val)

Set metadata for a symbolic expression in a given context.

# Arguments
- `s::Symbolic`: The symbolic expression
- `ctx::DataType`: The metadata context key
- `val`: The metadata value to set

# Returns
A new symbolic expression with the updated metadata

# Examples
```julia
julia> @syms x
x

julia> x_with_meta = setmetadata(x, Float64, "custom value")
x

julia> getmetadata(x_with_meta, Float64)
"custom value"
```
"""
function setmetadata(s::Symbolic, ctx::DataType, val)
    if s.metadata isa AbstractDict
        @set s.metadata = assocmeta(s.metadata, ctx, val)
    else
        # fresh Dict
        @set s.metadata = Base.ImmutableDict{DataType, Any}(ctx, unwrap(val))
    end
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
    if symtype(t) == LiteralReal
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

"""
    showraw([io::IO], t)

Display the raw structure of a symbolic expression without simplification.

This function shows the internal structure of symbolic expressions without applying
any simplification rules, which is useful for debugging and understanding the
exact form of an expression.

# Arguments
- `io::IO`: Optional IO stream to write to (defaults to stdout)
- `t`: The symbolic expression to display

# Examples
```julia
julia> @syms x
x

julia> expr = x + x + x
3x

julia> showraw(expr)  # Shows the unsimplified structure
x + x + x
```
"""
showraw(io, t) = Base.show(IOContext(io, :simplify=>false), t)
showraw(t) = showraw(stdout, t)

function Base.show(io::IO, v::BSImpl.Type)
    if issym(v)
        Base.show_unquoted(io, v.name)
    elseif isconst(v)
        printstyled(io, v.val; color = :blue)
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

function safe_add!(dict, coeff, b)
    if isadd(b)
        coeff += b.coeff
        for (k, v) in b.dict
            dict[k] = get(dict, k, 0) + v
        end
    elseif ismul(b)
        v = b.coeff
        metadata = b.metadata
        if metadata === nothing
            b′ = Mul{symtype(b)}(1, b.dict)
        else
            b′ = Mul{symtype(b)}(1, b.dict; metadata)
        end
        dict[b′] = get(dict, b′, 0) + v
    elseif b isa Number
        coeff += b
    else
        dict[b] = get(dict, b, 0) + 1
    end
    return coeff
end

function +(a::SN, bs::SN...)
    add_worker((a, bs...))
end

function add_worker(terms)
    a, bs = Iterators.peel(terms)
    isempty(bs) && return a
    T = symtype(a)
    for b in bs
        T = promote_symtype(+, T, symtype(b))
    end
    # entries where `!issafecanon`
    unsafes = SmallV{Any}()
    # coeff and dict of the `Add`
    coeff = 0
    dict = Dict{Symbolic, T}()
    # type of the `Add`

    # handle `a` separately
    if issafecanon(+, a)
        if isadd(a)
            coeff = a.coeff
            dict = copy(a.dict)
        elseif ismul(a)
            v = a.coeff
            a′ = Mul{symtype(a)}(1, a.dict; metadata = a.metadata)
            dict[a′] = v
        elseif a isa Number
            coeff = a
        else
            dict[a] = 1
        end
    else
        push!(unsafes, a)
    end

    for b in bs
        if !issafecanon(+, b)
            push!(unsafes, b)
            continue
        end
        coeff = safe_add!(dict, coeff, b)
    end
    # remove entries multiplied by zero
    filter!(dict) do kvp
        !iszero(kvp[2])
    end
    if isempty(dict)
        result = coeff
    elseif iszero(coeff) && length(dict) == 1
        expr, coeff = first(dict)
        result = coeff * expr
    else
        result = Add{T}(coeff, dict)
    end
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
    T  = add_t(a, b)
    if isadd(b)
        Add{T}(a + b.coeff, b.dict)
    else
        Add{T}(makeadd(T, a, b)...)
    end
end

function +(a::SN, b::Number, bs::SN...)
    return +(b, a, bs...)
end

function -(a::SN)
    !issafecanon(*, a) && return term(-, a)
    isadd(a) ? Add{sub_t(a)}(-a.coeff, mapvalues((_,v) -> -v, a.dict)) : (-1 * a)
end

function -(a::SN, b::SN)
    (!issafecanon(+, a) || !issafecanon(*, b)) && return term(-, a, b)
    isadd(a) && isadd(b) ? Add{sub_t(a,b)}(
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

# should not be called with a `div`
function get_mul_coeff_dict(::Type{T}, term; safe = false) where {T}
    @match term begin
        x::Number => (x, Dict{Symbolic, T}())
        BSImpl.AddOrMul(; variant = AddMulVariant.MUL, coeff, dict) => (coeff, copy(dict))
        BSImpl.Pow(; base, exp) && if exp isa Number end => (1, Dict{Symbolic, T}(base => exp))
        _ => (1, Dict{Symbolic, T}(term => 1))
    end
end

function mul_worker(terms)
    length(terms) == 1 && return only(terms)
    a, bs = Iterators.peel(terms)
    a = unwrap(a)
    T = symtype(a)
    for b in bs
        T = promote_symtype(*, T, symtype(b))
    end
    unsafes = SmallV{Any}()
    if isdiv(a)
        num_coeff, num_dict = get_mul_coeff_dict(T, a.num)
        den_coeff, den_dict = get_mul_coeff_dict(T, a.den)
    elseif !issafecanon(*, a)
        push!(unsafes, a)
        num_coeff, num_dict = 1, Dict{Symbolic, T}()
        den_coeff, den_dict = 1, nothing
    else
        num_coeff, num_dict = get_mul_coeff_dict(T, a)
        den_coeff = 1
        den_dict = nothing
    end

    for b in bs
        b = unwrap(b)
        if !issafecanon(*, b)
            push!(unsafes, b)
            continue
        end
        @match b begin
            x::Number => (num_coeff *= x)
            BSImpl.AddOrMul(; variant = AddMulVariant.MUL, coeff, dict) => begin
                num_coeff *= coeff
                for (k, v) in dict
                    num_dict[k] = get(num_dict, k, 0) + v
                end
            end
            BSImpl.Pow(; base, exp) && if exp isa Number end => begin
                num_dict[base] = get(num_dict, base, 0) + exp
            end
            BSImpl.Div(; num, den) => begin
                if den_dict === nothing && !(den isa Number)
                    den_dict = Dict{Symbolic, T}()
                end
                @match num begin
                    x::Number => (num_coeff *= x)
                    BSImpl.AddOrMul(; variant = AddMulVariant.MUL, coeff, dict) => begin
                        num_coeff *= coeff
                        for (k, v) in dict
                            num_dict[k] = get(num_dict, k, 0) + v
                        end
                    end
                    BSImpl.Pow(; base, exp) && if exp isa Number end => begin
                        num_dict[base] = get(num_dict, base, 0) + exp
                    end
                    _ => (num_dict[num] = get(num_dict, num, 0) + 1)
                end
                @match den begin
                    x::Number => (den_coeff *= x)
                    BSImpl.AddOrMul(; variant = AddMulVariant.MUL, coeff, dict) => begin
                        den_coeff *= coeff
                        for (k, v) in dict
                            den_dict[k] = get(den_dict, k, 0) + v
                        end
                    end
                    BSImpl.Pow(; base, exp) && if exp isa Number end => begin
                        den_dict[base] = get(den_dict, base, 0) + exp
                    end
                    _ => (den_dict[den] = get(den_dict, den, 0) + 1)
                end
            end
            _ => (num_dict[b] = get(num_dict, b, 0) + 1)
        end
    end

    if iszero(num_coeff)
        return num_coeff
    end
    filter!(kvp -> !iszero(kvp[2]), num_dict)
    if isempty(num_dict)
        num = num_coeff
    elseif isone(num_coeff) && length(num_dict) == 1
        base, exp = first(num_dict)
        num = Pow{T}(base, exp)
    elseif isone(-num_coeff) && length(num_dict) == 1 && isadd(first(keys(num_dict))) && isone(first(values(num_dict)))
        add_term, _ = first(num_dict)
        coeff = -add_term.coeff
        dict = copy(add_term.dict)
        map!(x -> -x, values(dict))
        num = Add{T}(coeff, dict; metadata = metadata(add_term))
    else
        num = Mul{T}(num_coeff, num_dict)
    end

    if !isempty(unsafes)
        push!(unsafes, num)
        num = Term{T}(*, unsafes)
    end

    if den_dict !== nothing
        filter!(kvp -> !iszero(kvp[2]), den_dict)
    end

    if den_dict === nothing || isempty(den_dict)
        den = den_coeff
    elseif isone(den_coeff) && length(den_dict) == 1
        base, exp = first(den_dict)
        den = Pow{T}(base, exp)
    elseif isone(-den_coeff) && length(den_dict) == 1 && isadd(first(keys(den_dict))) && isone(first(values(den_dict)))
        add_term, _ = first(den_dict)
        coeff = -add_term.coeff
        dict = copy(add_term.dict)
        map!(x -> -x, values(dict))
        den = Add{T}(coeff, dict; metadata = metadata(add_term))
    else
        den = Mul{T}(den_coeff, den_dict)
    end

    return Div{T}(num, den, false)
end

function *(a::SN, b::SN)
    mul_worker((a, b))
end

function *(a::Number, b::SN)
    mul_worker((a, b))
end

###
### Div
###

/(a::Union{SN,Number}, b::SN) = Div(a, b, false)

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
    elseif b isa Real && b < 0
        Div(1, a ^ (-b), false)
    elseif ismul(a) && b isa Number
        coeff = ^(a.coeff, b)
        Mul{promote_symtype(^, symtype(a), symtype(b))}(
            coeff, mapvalues((k, v) -> b*v, a.dict))
    else
        Pow(a, b)
    end
end

^(a::Number, b::SN) = Pow(a, b)
