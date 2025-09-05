export SymReal, SafeReal, TreeReal, vartype

abstract type SymVariant end
abstract type SymReal <: SymVariant end
abstract type SafeReal <: SymVariant end
abstract type TreeReal <: SymVariant end

###
### Uni-type design
###

# Unknown(0) is an array of unknown ndims
# Empty ShapeVecT is a scalar
struct Unknown
    ndims::Int
end

const MetadataT = Union{Base.ImmutableDict{DataType, Any}, Nothing}
const SmallV{T} = SmallVec{T, Vector{T}}
const ShapeVecT = SmallV{UnitRange{Int}}
const ShapeT = Union{Unknown, ShapeVecT}
const IdentT = Union{Tuple{UInt, IDType}, Tuple{Nothing, Nothing}}
const MonomialOrder = MP.Graded{MP.Reverse{MP.InverseLexOrder}}
const PolyVarOrder = DP.Commutative{DP.CreationOrder}
const ExamplePolyVar = only(DP.@polyvar __DUMMY__ monomial_order=MonomialOrder)
const PolyVarT = typeof(ExamplePolyVar)
const PolyCoeffT = Number
const _PolynomialT{T} = DP.Polynomial{PolyVarOrder, MonomialOrder, T}
# we can't actually print a zero polynomial of this type, since it attempts to call
# `zero(Any)` but that doesn't matter because we shouldn't ever store a zero polynomial
const PolynomialT = _PolynomialT{PolyCoeffT}
const TypeT = Union{DataType, UnionAll, Union}

function zeropoly()
    mv = DP.MonomialVector{PolyVarOrder, MonomialOrder}()
    PolynomialT(PolyCoeffT[], mv)
end

function onepoly()
    V = DP.Commutative{DP.CreationOrder}
    mv = DP.MonomialVector{V, MonomialOrder}(DP.Variable{V, MonomialOrder}[], [Int[]])
    PolynomialT(PolyCoeffT[1], mv)
end

@enumx AddMulVariant::Bool begin
    ADD
    MUL
end

"""
    $(TYPEDEF)

Core ADT for `BasicSymbolic`. `hash` and `isequal` compare metadata.
"""
@data mutable BasicSymbolicImpl{T <: SymVariant} begin 
    struct Const
        const val::Any
        id::IdentT
    end
    struct Sym
        const name::Symbol
        const metadata::MetadataT
        const shape::ShapeT
        const type::TypeT
        hash::UInt
        hash2::UInt
        id::IdentT
    end
    struct Term
        const f::Any
        const args::SmallV{BasicSymbolicImpl.Type{T}}
        const metadata::MetadataT
        const shape::ShapeT
        const type::TypeT
        hash::UInt
        hash2::UInt
        id::IdentT
    end
    struct AddMul
        const coeff::Any
        const dict::Dict{BasicSymbolicImpl.Type{T}, Number}
        const variant::AddMulVariant.T
        const metadata::MetadataT
        const shape::ShapeT
        const type::TypeT
        const args::SmallV{BasicSymbolicImpl.Type{T}}
        hash::UInt
        hash2::UInt
        id::IdentT
    end
    struct Div
        const num::BasicSymbolicImpl.Type{T}
        const den::BasicSymbolicImpl.Type{T}
        # TODO: Keep or remove?
        # Flag for whether this div is in the most simplified form we can compute.
        # This being false doesn't mean no elimination is performed. Trivials such as
        # constant factors can be eliminated. However, polynomial elimination may not
        # have been performed yet. Typically used as an early-exit for simplification
        # algorithms to not try to eliminate more.
        const simplified::Bool
        const metadata::MetadataT
        const shape::ShapeT
        const type::TypeT
        hash::UInt
        hash2::UInt
        id::IdentT
    end
end

const BSImpl = BasicSymbolicImpl
const BasicSymbolic = BSImpl.Type
const ArgsT{T} = SmallV{BasicSymbolic{T}}
const ROArgsT{T} = ReadOnlyVector{BasicSymbolic{T}, ArgsT{T}}
const ACDict{T} = Dict{BasicSymbolic{T}, Number}

const POLYVAR_LOCK = ReadWriteLock()
# NOTE: All of these are accessed via POLYVAR_LOCK
const BS_TO_PVAR = WeakKeyDict{BasicSymbolic, PolyVarT}()

# TODO: manage scopes better here
function basicsymbolic_to_polyvar(x::BasicSymbolic)::PolyVarT
    pvar = nothing
    @readlock POLYVAR_LOCK begin
        pvar = get(BS_TO_PVAR, x, nothing)
    end
    if pvar !== nothing
        return pvar
    end
    inner_name = _name_as_operator(x)
    name = Symbol(inner_name, :_, hash(x))
    pvar = MP.similar_variable(ExamplePolyVar, name)
    @lock POLYVAR_LOCK begin
        BS_TO_PVAR[x] = pvar
    end
    return pvar
end

function subs_poly(poly::Union{_PolynomialT, MP.Term}, vars::AbstractVector{BasicSymbolic{T}}) where {T}
    add_buffer = ArgsT{T}()
    mul_buffer = ArgsT{T}()
    for term in MP.terms(poly)
        empty!(mul_buffer)
        coeff = MP.coefficient(term)
        push!(mul_buffer, Const{T}(coeff))
        mono = MP.monomial(term)
        for (i, exp) in enumerate(MP.exponents(mono))
            iszero(exp) && continue
            push!(mul_buffer, (vars[i] ^ exp))
        end
        push!(add_buffer, mul_worker(T, mul_buffer))
    end
    return add_worker(T, add_buffer)
end
function subs_poly(poly::PolyVarT, vars::AbstractVector{BasicSymbolic{T}}) where {T}
    return only(vars)
end

function symtype(x::BasicSymbolic)
    # use `@match` instead of `x.type` since it is faster
    @match x begin
        BSImpl.Const(; val) => typeof(val)
        BSImpl.Sym(; type) => type
        BSImpl.Term(; type) => type
        BSImpl.AddMul(; type) => type
        BSImpl.Div(; type) => type
    end
end
symtype(x) = typeof(x)

vartype(x::BasicSymbolic{T}) where {T} = T
vartype(::Type{BasicSymbolic{T}}) where {T} = T

Base.@nospecializeinfer @generated function _shape_notsymbolic(x)
    @nospecialize x
    
    expr = Expr(:if)
    cur_expr = expr
    i = 0
    N = length(SCALARS)
    for t1 in SCALARS
        for T in [t1, Vector{t1}, Matrix{t1}, LinearAlgebra.UniformScaling{t1}]
            i += 1
            push!(cur_expr.args, :(x isa $T))
            push!(cur_expr.args, T <: LinearAlgebra.UniformScaling ? Unknown(2) : :($ShapeVecT(axes(x))))
            new_expr = Expr(:elseif)
            push!(cur_expr.args, new_expr)
            cur_expr = new_expr
        end
    end
    push!(cur_expr.args, :(x isa $(LinearAlgebra.UniformScaling)))
    push!(cur_expr.args, Unknown(2))
    push!(cur_expr.args, :($ShapeVecT(axes(x))))
    quote
        @nospecialize x
        $expr
    end
end

function shape(x::BasicSymbolic)
    # use `@match` instead of `x.type` since it is faster
    @match x begin
        BSImpl.Const(; val) => _shape_notsymbolic(val)::ShapeT
        BSImpl.Sym(; shape) => shape
        BSImpl.Term(; shape) => shape
        BSImpl.AddMul(; shape) => shape
        BSImpl.Div(; shape) => shape
    end
end

shape(x) = _shape_notsymbolic(x)::ShapeT
shape(::Colon) = ShapeVecT((1:0,))

function SymbolicIndexingInterface.symbolic_type(x::BasicSymbolic)
    symtype(x) <: AbstractArray ? ArraySymbolic() : ScalarSymbolic()
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
        ::Type{<:BSImpl.Const} => (; id = (nothing, nothing))
        ::Type{<:BSImpl.Sym} => (; id = (nothing, nothing), hash = 0, hash2 = 0)
        ::Type{<:BSImpl.AddMul} => (; id = (nothing, nothing), hash = 0, hash2 = 0)
        ::Type{<:BSImpl.Term} => (; id = (nothing, nothing), hash = 0, hash2 = 0)
        ::Type{<:BSImpl.Div} => (; id = (nothing, nothing), hash = 0, hash2 = 0)
        _ => throw(UnimplementedForVariantError(override_properties, obj))
    end
end

ordered_override_properties(::Type{<:BSImpl.Const}) = ((nothing, nothing),)
ordered_override_properties(::Type{<:BSImpl.Sym}) = (0, 0, (nothing, nothing))
ordered_override_properties(::Type{<:BSImpl.Term}) = (0, 0, (nothing, nothing))
ordered_override_properties(::Type{BSImpl.AddMul{T}}) where {T} = (ArgsT{T}(), 0, 0, (nothing, nothing))
ordered_override_properties(::Type{<:BSImpl.Div}) = (0, 0, (nothing, nothing))

function ConstructionBase.getproperties(obj::BSImpl.Type)
    @match obj begin
        BSImpl.Const(; val, id) => (; val, id)
        BSImpl.Sym(; name, metadata, hash, hash2, shape, type, id) => (; name, metadata, hash, hash2, shape, type, id)
        BSImpl.Term(; f, args, metadata, hash, hash2, shape, type, id) => (; f, args, metadata, hash, hash2, shape, type, id)
        BSImpl.AddMul(; coeff, dict, variant, metadata, shape, type, args, hash, hash2, id) => (; coeff, dict, variant, metadata, shape, type, args, hash, hash2, id)
        BSImpl.Div(; num, den, simplified, metadata, hash, hash2, shape, type, id) => (; num, den, simplified, metadata, hash, hash2, shape, type, id)
    end
end

function ConstructionBase.setproperties(obj::BSImpl.Type{T}, patch::NamedTuple) where {T}
    props = getproperties(obj)
    overrides = override_properties(obj)
    # We only want to invalidate `args` if we're updating `coeff` or `dict`.
    if isaddmul(obj)
        extras = (; args = ArgsT{T}())
    else
        extras = (;)
    end
    hashcons(MData.variant_type(obj)(; props..., patch..., overrides..., extras...)::BasicSymbolic{T})
end

###
### Term interface
###

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
@inline function TermInterface.operation(x::BSImpl.Type)
    @nospecialize x
    @match x begin
        BSImpl.Const(_) => throw(ArgumentError("`Const` does not have an operation."))
        BSImpl.Sym(_) => throw(ArgumentError("`Sym` does not have an operation."))
        BSImpl.Term(; f) => f
        BSImpl.AddMul(; variant) => @match variant begin
            AddMulVariant.ADD => (+)
            AddMulVariant.MUL => (*)
        end
        BSImpl.Div(_) => (/)
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
    T = vartype(x)
    @match x begin
        BSImpl.AddMul(; variant) => begin
            args = copy(parent(arguments(x)))
            @match variant begin
                AddMulVariant.ADD => sort!(args; by = get_degrees, lt = monomial_lt)
                AddMulVariant.MUL => sort!(args; by = get_degrees)
            end
            return ROArgsT{T}(ArgsT{T}(args))
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
function TermInterface.arguments(x::BSImpl.Type{T})::ROArgsT{T} where {T}
    @match x begin
        BSImpl.Const(_) => throw(ArgumentError("`Const` does not have arguments."))
        BSImpl.Sym(_) => throw(ArgumentError("`Sym` does not have arguments."))
        BSImpl.Term(; args) => ROArgsT{T}(args)
        BSImpl.AddMul(; coeff, dict, variant, args, shape, type) => begin
            isempty(args) || return ROArgsT{T}(args)
            @match variant begin
                AddMulVariant.ADD => begin
                    if !iszero(coeff)
                        push!(args, Const{T}(coeff))
                    end
                    for (k, v) in dict
                        newterm = @match k begin
                            BSImpl.AddMul(; dict = d2, variant = v2, type, shape, metadata) && if v2 == AddMulVariant.MUL end => begin
                                Mul{T}(v, d2; shape, type, metadata)
                            end
                            _ => Mul{T}(v, ACDict{T}(k => 1); shape, type)
                        end
                        push!(args, newterm)
                    end
                end
                AddMulVariant.MUL => begin
                    if !isone(coeff)
                        push!(args, Const{T}(coeff))
                    end
                    for (k, v) in dict
                        push!(args, k ^ v)
                    end
                end
            end
            return ROArgsT{T}(args)
        end
        BSImpl.Div(num, den) => ROArgsT{T}(ArgsT{T}((num, den)))
        _ => throw(UnimplementedForVariantError(arguments, MData.variant_type(x)))
    end
end

function addmul_variant(x::BasicSymbolic)
    @match x begin
        BSImpl.AddMul(; variant) => variant
    end
end

function isexpr(s::BSImpl.Type)
    !MData.isa_variant(s, BSImpl.Sym) && !MData.isa_variant(s, BSImpl.Const)
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

isconst(x::BSImpl.Type) = MData.isa_variant(x, BSImpl.Const)
issym(x::BSImpl.Type) = MData.isa_variant(x, BSImpl.Sym)
isterm(x::BSImpl.Type) = MData.isa_variant(x, BSImpl.Term)
isaddmul(x::BSImpl.Type) = MData.isa_variant(x, BSImpl.AddMul)
isadd(x::BSImpl.Type) = isaddmul(x) && addmul_variant(x) == AddMulVariant.ADD
ismul(x::BSImpl.Type) = isaddmul(x) && addmul_variant(x) == AddMulVariant.MUL
isdiv(x::BSImpl.Type) = MData.isa_variant(x, BSImpl.Div)
ispow(x::BSImpl.Type) = isterm(x) && operation(x) === (^)

for fname in [:isconst, :issym, :isterm, :isaddmul, :isadd, :ismul, :isdiv, :ispow]
    @eval $fname(x) = false
end

###
### Base interface
###

Base.isequal(::BasicSymbolic, x) = false
Base.isequal(x, ::BasicSymbolic) = false
Base.isequal(::BasicSymbolic, ::Missing) = false
Base.isequal(::Missing, ::BasicSymbolic) = false

const COMPARE_FULL = TaskLocalValue{Bool}(Returns(false))

const SCALARS = [Bool, Int, Int32, BigInt, Float64, Float32, BigFloat, Rational{Int}, Rational{Int32}, Rational{BigInt}, ComplexF32, ComplexF64, Complex{BigFloat}]

@generated function isequal_somescalar(a, b)
    @nospecialize a b
    
    expr = Expr(:if)
    cur_expr = expr

    N = length(SCALARS)
    for (i, (t1, t2)) in enumerate(Iterators.product(SCALARS, SCALARS))
        push!(cur_expr.args, :(a isa $t1 && b isa $t2))
        push!(cur_expr.args, :(isequal(a, b)))
        i == N * N && continue
        new_expr = Expr(:elseif)
        push!(cur_expr.args, new_expr)
        cur_expr = new_expr
    end
    
    push!(cur_expr.args, :(isequal(a, b)::Bool))
    quote
        @nospecialize a b
        $expr
    end
end

function isequal_addmuldict(d1::ACDict{T}, d2::ACDict{T}, full) where {T}
    full || return isequal(d1, d2)
    length(d1) == length(d2) || return false
    for (k, v) in d1
        k2 = nothing
        v2 = nothing
        @manually_scope COMPARE_FULL => false begin
            k2 = getkey(d2, k, nothing)
            k2 === nothing && return false
            v2 = d2[k2]
        end true
        isequal_somescalar(v, v2) && isequal_bsimpl(k, k2, true) || return false
    end
    return true
end

isequal_bsimpl(::BSImpl.Type, ::BSImpl.Type, ::Bool) = false

function isequal_bsimpl(a::BSImpl.Type{T}, b::BSImpl.Type{T}, full::Bool) where {T}
    a === b && return true
    taskida, ida = a.id
    taskidb, idb = b.id
    ida === idb && ida !== nothing && return true

    Ta = MData.variant_type(a)
    Tb = MData.variant_type(b)
    Ta === Tb || return false

    if full && ida !== idb && ida !== nothing && idb !== nothing && taskida == taskidb
        return false
    end

    partial = @match (a, b) begin
        (BSImpl.Const(; val = v1), BSImpl.Const(; val = v2)) => begin
            isequal(v1, v2)::Bool && (!full || (typeof(v1) === typeof(v2))::Bool)
        end
        (BSImpl.Sym(; name = n1, shape = s1, type = t1), BSImpl.Sym(; name = n2, shape = s2, type = t2)) => begin
            n1 === n2 && s1 == s2 && t1 === t2
        end
        (BSImpl.Term(; f = f1, args = args1, shape = s1, type = t1), BSImpl.Term(; f = f2, args = args2, shape = s2, type = t2)) => begin
            isequal(f1, f2) && isequal(args1, args2) && s1 == s2 && t1 === t2
        end
        (BSImpl.AddMul(; coeff = c1, dict = d1, variant = v1, shape = s1, type = t1), BSImpl.AddMul(; coeff = c2, dict = d2, variant = v2, shape = s2, type = t2)) => begin
            isequal(c1, c2) && isequal_addmuldict(d1, d2, full) && isequal(v1, v2) && s1 == s2 && t1 === t2
        end
        (BSImpl.Div(; num = n1, den = d1, type = t1), BSImpl.Div(; num = n2, den = d2, type = t2)) => begin
            isequal_bsimpl(n1, n2, full) && isequal_bsimpl(d1, d2, full) && t1 === t2
        end
    end
    if full && partial && !(Ta <: BSImpl.Const)
        partial = isequal(metadata(a), metadata(b))
    end
    return partial
end

function Base.isequal(a::BSImpl.Type, b::BSImpl.Type)
    isequal_bsimpl(a, b, COMPARE_FULL[])
end

Base.isequal(a::BSImpl.Type, b::WeakRef) = isequal(a, b.value)
Base.isequal(a::WeakRef, b::BSImpl.Type) = isequal(a.value, b)

const SYM_SALT = 0x4de7d7c66d41da43 % UInt
const DIV_SALT = 0x334b218e73bbba53 % UInt

@generated function hash_somescalar(a, h::UInt)
    @nospecialize a
    expr = Expr(:if)
    cur_expr = expr

    N = length(SCALARS)
    for (i, t1) in enumerate(SCALARS)
        push!(cur_expr.args, :(a isa $t1))
        push!(cur_expr.args, :(hash(a, h)))
        i == N && continue
        new_expr = Expr(:elseif)
        push!(cur_expr.args, new_expr)
        cur_expr = new_expr
    end
    
    push!(cur_expr.args, :(hash(a, h)::UInt))
    quote
        @nospecialize a
        $expr
    end
end

function hash_addmuldict(d::ACDict, h::UInt, full::Bool)
    hv = Base.hasha_seed
    for (k, v) in d
        h1 = hash_somescalar(v, zero(UInt))
        h1 = hash_bsimpl(k, h1, full)
        hv ⊻= h1
    end
    return hash(hv, h)
end

function hash_bsimpl(s::BSImpl.Type{T}, h::UInt, full) where {T}
    if !iszero(h)
        return hash(hash_bsimpl(s, zero(h), full), h)::UInt
    end
    h = hash(T, h)

    partial::UInt = @match s begin
        BSImpl.Const(; val) => begin
            h = hash_somescalar(val, h)::UInt
            if full
                h = Base.hash(typeof(val), h)::UInt
            end
            return h
        end
        BSImpl.Sym(; name, shape, type, hash, hash2) => begin
            full && !iszero(hash2) && return hash2
            !full && !iszero(hash) && return hash
            h = Base.hash(name, h)
            h = Base.hash(shape, h)
            h = Base.hash(type, h)
            h ⊻ SYM_SALT
        end
        BSImpl.Term(; f, args, shape, hash, hash2, type) => begin
            full && !iszero(hash2) && return hash2
            !full && !iszero(hash) && return hash
            Base.hash(f, Base.hash(args, Base.hash(shape, Base.hash(type, h))))::UInt
        end
        BSImpl.AddMul(; coeff, dict, variant, shape, type, hash, hash2) => begin
            full && !iszero(hash2) && return hash2
            !full && !iszero(hash) && return hash
            hash_somescalar(coeff, hash_addmuldict(dict, Base.hash(variant, Base.hash(shape, Base.hash(type, h))), full))
        end
        BSImpl.Div(; num, den, type, hash, hash2) => begin
            full && !iszero(hash2) && return hash2
            !full && !iszero(hash) && return hash
            Base.hash(num, Base.hash(den, Base.hash(type, h))) ⊻ DIV_SALT
        end
    end

    if full
        partial = s.hash2 = Base.hash(metadata(s), partial)::UInt
    else
        s.hash = partial
    end
    return partial
end

function Base.hash(s::BSImpl.Type, h::UInt)
    hash_bsimpl(s, h, COMPARE_FULL[])
end

Base.one( s::BSImpl.Type) = one( symtype(s))
Base.zero(s::BSImpl.Type) = zero(symtype(s))

function _name_as_operator(x::BasicSymbolic)
    @match x begin
        BSImpl.Sym(; name) => name
        BSImpl.Term(; f) => _name_as_operator(f)
        _ => _name_as_operator(operation(x))
    end
end
_name_as_operator(x) = nameof(x)

Base.nameof(s::BasicSymbolic) = issym(s) ? s.name : error("Non-Sym BasicSymbolic doesn't have a name")

###
### Constructors
###

# TODO: split into 3 caches based on `SymVariant`
const ENABLE_HASHCONSING = Ref(true)
const AllBasicSymbolics = Union{BasicSymbolic{SymReal}, BasicSymbolic{SafeReal}, BasicSymbolic{TreeReal}}
const WCS = TaskLocalValue{WeakCacheSet{AllBasicSymbolics}}(WeakCacheSet{AllBasicSymbolics})
const TASK_ID = TaskLocalValue{UInt}(() -> rand(UInt))

function generate_id()
    return (TASK_ID[], IDType())
end

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

function hashcons(s::BSImpl.Type)
    if !ENABLE_HASHCONSING[]
        return s
    end
    @manually_scope COMPARE_FULL => true begin
        cache = WCS[]
        k = getkey!(cache, s)::typeof(s)
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
        if k.id === (nothing, nothing)
            k.id = generate_id()
        end
        return k::typeof(s)
    end true
end

const SMALLV_DEFAULT_SYMREAL = hashcons(BSImpl.Const{SymReal}(0, (nothing, nothing)))
const SMALLV_DEFAULT_SAFEREAL = hashcons(BSImpl.Const{SafeReal}(0, (nothing, nothing)))
const SMALLV_DEFAULT_TREEREAL = hashcons(BSImpl.Const{TreeReal}(0, (nothing, nothing)))

defaultval(::Type{BasicSymbolic{SymReal}}) = SMALLV_DEFAULT_SYMREAL
defaultval(::Type{BasicSymbolic{SafeReal}}) = SMALLV_DEFAULT_SAFEREAL
defaultval(::Type{BasicSymbolic{TreeReal}}) = SMALLV_DEFAULT_TREEREAL

function get_mul_coefficient(x)
    iscall(x) && operation(x) === (*) || throw(ArgumentError("$x is not a multiplication"))
    @match x begin
        BSImpl.Term(; args) => begin
            if ismul(args[1])
                return get_mul_coefficient(args[1])
            else
                return 1
            end
        end
        BSImpl.AddMul(; coeff) => return coeff
    end
end

parse_metadata(x::MetadataT) = x
parse_metadata(::Nothing) = nothing
function parse_metadata(x)
    meta = MetadataT()
    for kvp in x
        meta = Base.ImmutableDict(meta, kvp)
    end
    return meta
end

default_shape(::Type{T}) where {E, N, T <: AbstractArray{E, N}} = Unknown(N)
default_shape(::Type{T}) where {T <: AbstractArray} = Unknown(0)
default_shape(_) = ShapeVecT()

"""
    $(METHODLIST)

If `x` is a rational with denominator 1, turn it into an integer.
"""
function maybe_integer(x)
    x = unwrap(x)
    return (x isa Rational && isone(x.den)) ? x.num : x
end

function parse_args(::Type{T}, args::Union{Tuple, AbstractVector}) where {T <: SymVariant}
    args isa ROArgsT{T} && return parent(args)::ArgsT{T}
    args isa ArgsT{T} && return args
    _args = ArgsT{T}()
    sizehint!(_args, length(args))
    for arg in args
        push!(_args, Const{T}(arg))
    end
    return _args::ArgsT{T}
end

function unwrap_args(args)
    if any(x -> unwrap(x) !== x, args)
        map(unwrap, args)
    else
        args
    end
end

function parse_dict(::Type{T}, dict::AbstractDict) where {T}
    dict isa ACDict{T} && return dict
    _dict = ACDict{T}()
    for (k, v) in dict
        _dict[k] = v
    end
end

function unwrap_dict(dict)
    if any(x -> unwrap(x) !== x, keys(dict))
        typeof(dict)(unwrap(k) => v for (k, v) in dict)
    else
        dict
    end
end

@inline function BSImpl.Const{T}(val; unsafe = false) where {T}
    @nospecialize val
    if val isa BasicSymbolic{T}
        return val
    elseif val isa BasicSymbolic{SymReal}
        error("Cannot construct `BasicSymbolic{$T}` from `BasicSymbolic{SymReal}`.")
    elseif val isa BasicSymbolic{SafeReal}
        error("Cannot construct `BasicSymbolic{$T}` from `BasicSymbolic{SymReal}`.")
    elseif val isa BasicSymbolic{TreeReal}
        error("Cannot construct `BasicSymbolic{$T}` from `BasicSymbolic{TreeReal}`.")
    else
        props = ordered_override_properties(BSImpl.Const)
        var = BSImpl.Const{T}(val, props...)
        if !unsafe
            var = hashcons(var)
        end
        return var
    end
end

@inline function BSImpl.Sym{T}(name::Symbol; metadata = nothing, type, shape = default_shape(type), unsafe = false) where {T}
    metadata = parse_metadata(metadata)
    props = ordered_override_properties(BSImpl.Sym)
    var = BSImpl.Sym{T}(name, metadata, shape, type, props...)
    if !unsafe
        var = hashcons(var)
    end
    return var
end

@inline function BSImpl.Term{T}(f, args; metadata = nothing, type, shape = default_shape(type), unsafe = false) where {T}
    metadata = parse_metadata(metadata)
    args = parse_args(T, args)
    props = ordered_override_properties(BSImpl.Term)
    var = BSImpl.Term{T}(f, args, metadata, shape, type, props...)
    if !unsafe
        var = hashcons(var)
    end
    return var
end

@inline function BSImpl.AddMul{T}(coeff, dict, variant::AddMulVariant.T; metadata = nothing, type, shape = default_shape(type), unsafe = false) where {T}
    metadata = parse_metadata(metadata)
    dict = parse_dict(T, dict)
    props = ordered_override_properties(BSImpl.AddMul{T})
    var = BSImpl.AddMul{T}(coeff, dict, variant, metadata, shape, type, props...)
    if !unsafe
        var = hashcons(var)
    end
    return var
end

@inline function BSImpl.Div{T}(num, den, simplified::Bool; metadata = nothing, type, shape = default_shape(type), unsafe = false) where {T}
    metadata = parse_metadata(metadata)
    num = Const{T}(num)
    den = Const{T}(den)
    props = ordered_override_properties(BSImpl.Div)
    var = BSImpl.Div{T}(num, den, simplified, metadata, shape, type, props...)
    if !unsafe
        var = hashcons(var)
    end
    return var
end

struct Const{T} end
struct Sym{T} end
struct Term{T} end
struct Add{T} end
struct Mul{T} end
struct Div{T} end

@inline Const{T}(val; kw...) where {T} = BSImpl.Const{T}(val; kw...)

@inline Sym{T}(name; kw...) where {T} = BSImpl.Sym{T}(name; kw...)

@inline function Term{T}(f, args; type = _promote_symtype(f, args), kw...) where {T}
    args = unwrap_args(args)
    BSImpl.Term{T}(f, args; type, kw...)
end

@inline function Add{T}(coeff, dict; kw...) where {T}
    coeff = unwrap(coeff)
    dict = unwrap_dict(dict)
    if isempty(dict)
        return Const{T}(coeff)
    elseif _iszero(coeff) && length(dict) == 1
        k, v = first(dict)
        if _isone(v)
            return k
        else
            return k * v
        end
    end

    BSImpl.AddMul{T}(coeff, dict, AddMulVariant.ADD; kw...)
end

@inline function Mul{T}(coeff, dict; kw...) where {T}
    coeff = unwrap(coeff)
    dict = unwrap_dict(dict)
    if isempty(dict)
        return Const{T}(coeff)
    elseif _iszero(coeff)
        return Const{T}(0)
    elseif _isone(coeff) && length(dict) == 1
        k, v = first(dict)
        if _isone(v)
            return k
        else
            return k ^ v
        end
    elseif _isone(-coeff) && length(dict) == 1
        k, v = first(dict)
        if _isone(v)
            @match k begin
                BSImpl.AddMul(; coeff = c2, dict = d2, variant) && if variant == AddMulVariant.ADD end => begin
                    empty!(dict)
                    for (k, v) in d2
                        dict[k] = -v
                    end
                    return BSImpl.AddMul{T}(-c2, dict, variant; kw...)
                end
                _ => nothing
            end
        end
    end

    BSImpl.AddMul{T}(coeff, dict, AddMulVariant.MUL; kw...)
end

const Rat = Union{Rational, Integer}

"""
    $(TYPEDSIGNATURES)

Return a tuple containing a boolean indicating whether `x` has a rational/integer factor
and the rational/integer factor (or `NaN` otherwise).
"""
function ratcoeff(x)
    if iscall(x) && operation(x) === (*)
        ratcoeff(get_mul_coefficient(x))
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
"""
function Div{T}(n, d, simplified; type = promote_symtype(/, symtype(n), symtype(d)), kw...) where {T}
    n = unwrap(n)
    d = unwrap(d)

    if !(type <: Number)
        _iszero(n) && return Const{T}(n)
        _isone(d) && return Const{T}(n)
        return BSImpl.Div{T}(n, d, simplified; type, kw...)
    end

    if !(T === SafeReal)
        n, d = quick_cancel(Const{T}(n), Const{T}(d))
    end
    n = unwrap_const(n)
    d = unwrap_const(d)

    _iszero(n) && return Const{T}(n)
    _isone(d) && return Const{T}(n)
    _iszero(d) && return Const{T}(1 // 0)

    if isdiv(n) && isdiv(d)
        return Div{T}(n.num * d.den, n.den * d.num, simplified; type, kw...)
    elseif isdiv(n)
        return Div{T}(n.num, n.den * d, simplified; type, kw...)
    elseif isdiv(d)
        return Div{T}(n * d.den, d.num, simplified; type, kw...)
    end

    d isa Number && _isone(-d) && return Const{T}(-n)
    n isa Rat && d isa Rat && return Const{T}(n // d)

    n, d = simplify_coefficients(n, d)

    _isone(d) && return Const{T}(n)
    _isone(-d) && return Const{T}(-n)

    BSImpl.Div{T}(n, d, simplified; type, kw...)
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

@inline function unwrap_const(x::Any)
    @nospecialize x
    if x isa BasicSymbolic{SymReal}
        @match x begin
            BSImpl.Const(; val) => val
            _ => x
        end
    elseif x isa BasicSymbolic{SafeReal}
        @match x begin
            BSImpl.Const(; val) => val
            _ => x
        end
    elseif x isa BasicSymbolic{TreeReal}
        @match x begin
            BSImpl.Const(; val) => val
            _ => x
        end
    else
        x
    end
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
function term(f, args...; vartype = SymReal, type = promote_symtype(f, symtype.(args)...))
    @nospecialize f
    Term{vartype}(f, args; type)
end

function TermInterface.maketerm(::Type{BasicSymbolic{T}}, head, args, metadata; type = _promote_symtype(head, args)) where {T}
    @nospecialize head
    args = unwrap_args(args)
    basicsymbolic(T, head, args, type, metadata)
end

function basicsymbolic(::Type{T}, f, args, type::TypeT, metadata) where {T}
    @nospecialize f type
    if f isa Symbol
        error("$f must not be a Symbol")
    end
    args = unwrap_args(args)
    if T === TreeReal
        @goto FALLBACK
    elseif type <: Number
        if f === (+)
            res = add_worker(T, args)
            if metadata !== nothing && (isadd(res) || (isterm(res) && operation(res) == (+)))
                @set! res.metadata = metadata
            end
            return res
        elseif f === (*)
            res = mul_worker(T, args)
            if metadata !== nothing && (ismul(res) || (isterm(res) && operation(res) == (*)))
                @set! res.metadata = metadata
            end
            return res
        elseif f === (/)
            @assert length(args) == 2
            res = args[1] / args[2]
            if metadata !== nothing && isdiv(res)
                @set! res.metadata = metadata
            end
            return res
        elseif f === (^) && length(args) == 2
            res = args[1] ^ args[2]
            if metadata !== nothing && ispow(res)
                @set! res.metadata = metadata
            end
            return res
        else
            @goto FALLBACK
        end
    else
        @label FALLBACK
        Term{T}(f, args; type, metadata=metadata)
    end
end

###
### Metadata
###
metadata(s::BSImpl.Type) = isconst(s) ? nothing : s.metadata
metadata(s::BasicSymbolic, meta) = Setfield.@set! s.metadata = meta

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
function hasmetadata(s::BasicSymbolic, ctx)
    metadata(s) isa AbstractDict && haskey(metadata(s), ctx)
end

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
function getmetadata(s::BasicSymbolic, ctx)
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
function getmetadata(s::BasicSymbolic, ctx, default)
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
function setmetadata(s::BasicSymbolic, ctx::DataType, val)
    if s.metadata isa AbstractDict
        @set s.metadata = assocmeta(s.metadata, ctx, val)
    else
        # fresh Dict
        @set s.metadata = Base.ImmutableDict{DataType, Any}(ctx, unwrap(val))
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

"""
    promote_shape(f, shs::ShapeT...)

The shape of the result of applying `f` to arguments of [`shape`](@ref) `shs...`.
"""
promote_shape(f, szs::ShapeT...) = Unknown(0)

#---------------------------
#---------------------------
#### Function-like variables
#---------------------------

struct FnType{X<:Tuple,Y,Z} end

function (f::BasicSymbolic{T})(args...) where {T}
    symtype(f) <: FnType || error("Sym $f is not callable. " *
          "Use @syms $f(var1, var2,...) to create it as a callable.")
    Term{T}(f, args; type = promote_symtype(f, symtype.(args)...), shape = f.shape)
end

fntype_X_Y(::Type{<: FnType{X, Y}}) where {X, Y} = (X, Y)

"""
    promote_symtype(f::FnType{X,Y}, arg_symtypes...)

The output symtype of applying variable `f` to arguments of symtype `arg_symtypes...`.
if the arguments are of the wrong type then this function will error.
"""
function promote_symtype(f::BasicSymbolic, args...)
    T = symtype(f)
    X, Y = fntype_X_Y(T)

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
### Arithmetic
###
const NonTreeSym = Union{BasicSymbolic{SymReal}, BasicSymbolic{SafeReal}}
# integration. Constructors of `Add, Mul, Pow...` from Base (+, *, ^, ...)

import Base: (+), (-), (*), (//), (/), (\), (^)

@generated function _numeric_or_arrnumeric_type(S::TypeT)
    @nospecialize S
    
    expr = Expr(:if)
    cur_expr = expr
    i = 0
    N = length(SCALARS)
    for t1 in SCALARS
        for T in [t1, Vector{t1}, Matrix{t1}, LinearAlgebra.UniformScaling{t1}]
            i += 1
            push!(cur_expr.args, :(S === $T))
            push!(cur_expr.args, true)
            i == 4N && continue
            new_expr = Expr(:elseif)
            push!(cur_expr.args, new_expr)
            cur_expr = new_expr
        end
    end
    push!(cur_expr.args, :(S <: Union{Number, AbstractArray{<:Number}}))
    quote
        @nospecialize S
        $expr
    end
end

function _numeric_or_arrnumeric_symtype(x)
    _numeric_or_arrnumeric_type(symtype(x))
end

@generated function _rational_or_arrrational_type(S::TypeT)
    @nospecialize S
    
    expr = Expr(:if)
    cur_expr = expr
    i = 0
    N = length(SCALARS)
    for t1 in SCALARS
        for T in [t1, Vector{t1}, Matrix{t1}, LinearAlgebra.UniformScaling{t1}]
            i += 1
            push!(cur_expr.args, :(S === $T))
            push!(cur_expr.args, t1 <: Rat)
            i == 4N && continue
            new_expr = Expr(:elseif)
            push!(cur_expr.args, new_expr)
            cur_expr = new_expr
        end
    end
    push!(cur_expr.args, :(S <: Union{Rat, AbstractArray{<:Rat}}))
    quote
        @nospecialize S
        $expr
    end
end

function _rational_or_arrrational_symtype(x)
    _rational_or_arrrational_type(symtype(x))
end

@noinline function throw_unequal_shape_error(x, y)
    throw(ArgumentError("Cannot add arguments of different sizes - encountered shapes $x and $y."))
end

promote_shape(::typeof(+), shape::ShapeT) = shape
function promote_shape(::typeof(+), sh1::ShapeT, sh2::ShapeT, shs::ShapeT...)
    @nospecialize sh1 sh2 shs
    nd1 = _ndims_from_shape(sh1)
    nd2 = _ndims_from_shape(sh2)
    nd1 == nd2 || throw_unequal_shape_error(sh1, sh2)
    if sh1 isa Unknown && sh2 isa Unknown
        promote_shape(+, sh1, shs...)
    elseif sh1 isa Unknown
        promote_shape(+, sh2, shs...)
    elseif sh2 isa Unknown
        promote_shape(+, sh1, shs...)
    else
        new_shape = ShapeVecT()
        sizehint!(new_shape, length(sh1))
        for (shi, shj) in zip(sh1, sh2)
            length(shi) == length(shj) || throw_unequal_shape_error(sh1, sh2)
            # resultant shape is always 1-indexed for consistency
            push!(new_shape, 1:length(shi))
        end
        promote_shape(+, new_shape, shs...)
    end
end
promote_shape(::typeof(-), args::ShapeT...) = promote_shape(+, args...)

function +(x::T...) where {T <: NonTreeSym}
    add_worker(vartype(T), x)
end

@noinline Base.@nospecializeinfer function promoted_symtype(op, terms)
    a, bs = Iterators.peel(terms)
    type::TypeT = symtype(a)
    for b in bs
        type = promote_symtype(op, type, symtype(b))
    end
    return type
end

mutable struct AddWorkerBuffer{T}
    dict::ACDict{T}
end

AddWorkerBuffer{T}() where {T} = AddWorkerBuffer{T}(ACDict{T}())

Base.empty!(awb::AddWorkerBuffer) = empty!(awb.dict)

const SYMREAL_ADDBUFFER = TaskLocalValue{AddWorkerBuffer{SymReal}}(AddWorkerBuffer{SymReal})
const SAFEREAL_ADDBUFFER = TaskLocalValue{AddWorkerBuffer{SafeReal}}(AddWorkerBuffer{SafeReal})

add_worker(::Type{SymReal}, terms) = SYMREAL_ADDBUFFER[](terms)
add_worker(::Type{SafeReal}, terms) = SAFEREAL_ADDBUFFER[](terms)

function _added_shape(terms::Tuple)
    promote_shape(+, ntuple(shape ∘ Base.Fix1(getindex, terms), Val(length(terms)))...)
end

function _added_shape(terms)
    isempty(terms) && return Unknown(0)
    length(terms) == 1 && return shape(terms[1])
    a, bs = Iterators.peel(terms)
    sh::ShapeT = shape(a)
    for t in bs
        sh = promote_shape(+, sh, shape(t))
    end
    return sh
end

function (awb::AddWorkerBuffer{T})(terms) where {T}
    if !all(_numeric_or_arrnumeric_symtype, terms)
        throw(MethodError(+, Tuple(terms)))
    end
    isempty(terms) && return Const{T}(0)
    if isone(length(terms))
        return Const{T}(only(terms))
    end
    empty!(awb)
    shape = _added_shape(terms)
    type = promoted_symtype(+, terms)
    newcoeff = 0
    result = awb.dict
    for term in terms
        term = unwrap(term)
        if term isa BasicSymbolic{T}
            @match term begin
                BSImpl.Const(; val) => (newcoeff += val)
                BSImpl.AddMul(; coeff, dict, variant, shape, type, metadata) => begin
                    @match variant begin
                        AddMulVariant.ADD => begin
                            newcoeff += coeff
                            for (k, v) in dict
                                result[k] = get(result, k, 0) + v
                            end
                        end
                        AddMulVariant.MUL => begin
                            newterm = Mul{T}(1, dict; shape, type, metadata)
                            result[newterm] = get(result, newterm, 0) + coeff
                        end
                    end
                end
                _ => begin
                    result[term] = get(result, term, 0) + 1
                end
            end
        elseif term isa BasicSymbolic{SymReal} || term isa BasicSymbolic{SafeReal} || term isa BasicSymbolic{TreeReal}
            error("Cannot operate on symbolics with different vartypes. Found `$T` and `$(vartype(term))`.")
        else
            newcoeff += term
        end
    end
    filter!(!(iszero ∘ last), result)
    isempty(result) && return Const{T}(newcoeff)
    var = Add{T}(newcoeff, result; type, shape)
    @match var begin
        BSImpl.AddMul(; dict) && if dict === result end => (awb.dict = ACDict{T}())
        _ => nothing
    end
    return var
end

function +(a::Number, b::T, bs::T...) where {T <: NonTreeSym}
    return add_worker(vartype(T), (a, b, bs...))
end

function +(a::T, b::Number, bs::T...) where {T <: NonTreeSym}
    return add_worker(vartype(T), (a, b, bs...))
end

function -(a::BasicSymbolic{T}) where {T}
    if !_numeric_or_arrnumeric_symtype(a)
        throw(MethodError(-, (symtype(a),)))
    end
    @match a begin
        BSImpl.Const(; val) => Const{T}(-val)
        _ => nothing
    end
    @match a begin
        BSImpl.AddMul(; coeff, dict, variant, shape, type) => begin
            @match variant begin
                AddMulVariant.ADD => begin
                    coeff = -coeff
                    dict = copy(dict)
                    map!(-, values(dict))
                    return BSImpl.AddMul{T}(coeff, dict, variant; shape, type)
                end
                AddMulVariant.MUL => begin
                    return BSImpl.AddMul{T}(-coeff, dict, variant; shape, type)
                end
            end
        end
        _ => (-1 * a)
    end
end

function -(a::S, b::S) where {S <: NonTreeSym}
    if !_numeric_or_arrnumeric_symtype(a) || !_numeric_or_arrnumeric_symtype(b)
        throw(MethodError(-, (a, b)))
    end
    T = vartype(S)
    @match (a, b) begin
        (BSImpl.Const(; val = val1), BSImpl.Const(; val = val2)) => begin
            return Const{T}(val1 - val2)
        end
        _ => return add_worker(T, (a, -b))
    end
end

-(a::Number, b::BasicSymbolic) = a + (-b)
-(a::BasicSymbolic, b::Number) = a + (-b)

*(a::BasicSymbolic) = a

@noinline function throw_expected_matrix(x)
    throw(ArgumentError("Expected matrix in multiplication, got argument of shape $x."))
end
@noinline function throw_expected_matvec(x)
    throw(ArgumentError("""
    Expected matrix or vector in multiplication, got argument of shape $x.
    """))
end
@noinline function throw_incompatible_shapes(x, y)
    throw(ArgumentError("""
    Encountered incompatible shapes $x and $y when multiplying.
    """))
end

_is_array_shape(sh::ShapeT) = sh isa Unknown || _ndims_from_shape(sh) > 0
function _multiplied_shape(shapes)
    first_arr = findfirst(_is_array_shape, shapes)
    first_arr === nothing && return ShapeVecT()
    last_arr::Int = findlast(_is_array_shape, shapes)
    first_arr == last_arr && return shapes[first_arr]

    sh1::ShapeT = shapes[first_arr]
    shend::ShapeT = shapes[last_arr]
    ndims_1 = _ndims_from_shape(sh1)
    ndims_end = _ndims_from_shape(shend)
    ndims_1 == 0 || ndims_1 == 2 || throw_expected_matrix(sh1)
    ndims_end <= 2 || throw_expected_matvec(shend)
    if ndims_end == 1
        result = shend
    elseif sh1 isa Unknown || shend isa Unknown
        result = Unknown(ndims_end)
    else
        result = ShapeVecT((first(sh1), last(shend)))
    end
    cur_shape = sh1
    is_matmatmul = true
    for i in (first_arr + 1):last_arr
        sh = shapes[i]
        ndims_sh = _ndims_from_shape(sh)
        _is_array_shape(sh) || continue
        ndims_sh <= 2 || throw_expected_matvec(shend)
        is_matmatmul || throw_incompatible_shapes(cur_shape, sh)
        is_matmatmul = ndims_sh != 1
        if cur_shape isa ShapeVecT && sh isa ShapeVecT
            if length(last(cur_shape)) != length(first(sh))
                throw_incompatible_shapes(cur_shape, sh)
            end
        end
        cur_shape = sh
    end

    return result
end

function promote_shape(::typeof(*), shs::ShapeT...)
    _multiplied_shape(shs)
end

function _multiplied_terms_shape(terms::Tuple)
    _multiplied_shape(ntuple(shape ∘ Base.Fix1(getindex, terms), Val(length(terms))))
end

function _multiplied_terms_shape(terms)
    shapes = SmallV{ShapeT}()
    sizehint!(shapes, length(terms))
    for t in terms
        push!(shapes, shape(t))
    end
    return _multiplied_shape(shapes)
end

function _split_arrterm_scalar_coeff(term::BasicSymbolic{T}) where {T}
    sh = shape(term)
    _is_array_shape(sh) || return term, Const{T}(1)
    @match term begin
        BSImpl.Term(; f, args, type) && if f === (*) && !_is_array_shape(shape(first(args))) end => begin
            if length(args) == 2
                return args[1], args[2]
            end
            rest = ArgsT{T}()
            sizehint!(rest, length(args) - 1)
            coeff, restargs = Iterators.peel(args)
            for arg in restargs
                push!(rest, arg)
            end
            return coeff, Term{T}(f, rest; type, shape = sh)
        end
        _ => (Const{T}(1), term)
    end
end

function _as_base_exp(term::BasicSymbolic{T}) where {T}
    @match term begin
        BSImpl.Term(; f, args) && if f === (^) && isconst(args[2]) end => (args[1], args[2])
        _ => (term, Const{T}(1))
    end
end

function _mul_worker!(::Type{T}, num_coeff, den_coeff, num_dict, den_dict, term) where {T}
    @nospecialize term
    if term isa BasicSymbolic{T}
        @match term begin
            BSImpl.Const(; val) => (num_coeff[] *= val)
            BSImpl.AddMul(; coeff, dict, variant) && if variant == AddMulVariant.MUL end => begin
                num_coeff[] *= coeff
                for (k, v) in dict
                    num_dict[k] = get(num_dict, k, 0) + v
                end
            end
            BSImpl.Term(; f, args) && if f === (^) && !isconst(args[1]) && isconst(args[2]) end => begin
                base, exp = args
                num_dict[base] = get(num_dict, base, 0) + unwrap_const(exp)
            end
            BSImpl.Div(; num, den) => begin
                _mul_worker!(T, num_coeff, den_coeff, num_dict, den_dict, num)
                _mul_worker!(T, den_coeff, num_coeff, den_dict, num_dict, den)
            end
            x => begin
                num_dict[x] = get(num_dict, x, 0) + 1
            end
        end
    elseif term isa BasicSymbolic{SymReal} || term isa BasicSymbolic{SafeReal}
        error("Cannot operate on symbolics with different vartypes. Found `$T` and `$(vartype(term))`.")
    else
        num_coeff[] *= term
    end
    return nothing
end

mutable struct MulWorkerBuffer{T}
    num_dict::ACDict{T}
    den_dict::ACDict{T}
    const num_coeff::Vector{PolyCoeffT}
    const den_coeff::Vector{PolyCoeffT}
end

function MulWorkerBuffer{T}() where {T}
    MulWorkerBuffer{T}(Dict{BasicSymbolic{T}, Any}(), Dict{BasicSymbolic{T}, Any}(), PolyCoeffT[1], PolyCoeffT[1])
end

function Base.empty!(mwb::MulWorkerBuffer)
    empty!(mwb.num_dict)
    empty!(mwb.den_dict)
    empty!(mwb.num_coeff)
    empty!(mwb.den_coeff)
    push!(mwb.num_coeff, 1)
    push!(mwb.den_coeff, 1)
    return mwb
end

const SYMREAL_MULBUFFER = TaskLocalValue{MulWorkerBuffer{SymReal}}(MulWorkerBuffer{SymReal})
const SAFEREAL_MULBUFFER = TaskLocalValue{MulWorkerBuffer{SafeReal}}(MulWorkerBuffer{SafeReal})

function (mwb::MulWorkerBuffer{T})(terms) where {T}
    if !all(_numeric_or_arrnumeric_symtype, terms)
        throw(MethodError(*, Tuple(terms)))
    end
    isempty(terms) && return Const{T}(1)
    length(terms) == 1 && return Const{T}(terms[1])
    empty!(mwb)
    newshape = _multiplied_terms_shape(terms)
    num_dict = mwb.num_dict
    num_coeff = mwb.num_coeff
    den_dict = mwb.den_dict
    den_coeff = mwb.den_coeff

    type = promoted_symtype(*, terms)
    arrterms = ArgsT{T}()

    for term in terms
        term = unwrap(term)
        sh = shape(term)
        if _is_array_shape(sh)
            coeff, arrterm = _split_arrterm_scalar_coeff(term)
            _mul_worker!(T, num_coeff, den_coeff, num_dict, den_dict, coeff)
            if iscall(arrterm) && operation(arrterm) == (*)
                append!(arrterms, arguments(arrterm))
            else
                push!(arrterms, arrterm)
            end
            continue
        end
        _mul_worker!(T, num_coeff, den_coeff, num_dict, den_dict, term)
    end
    for k in keys(num_dict)
        haskey(den_dict, k) || continue
        numexp = num_dict[k]
        denexp = den_dict[k]
        if numexp >= denexp
            num_dict[k] = numexp - denexp
            den_dict[k] = 0
        else
            num_dict[k] = 0
            den_dict[k] = denexp - numexp
        end
    end
    filter!(kvp -> !iszero(kvp[2]), num_dict)
    filter!(kvp -> !iszero(kvp[2]), den_dict)
    num = Mul{T}(num_coeff[], num_dict; type = eltype(type))
    @match num begin
        BSImpl.AddMul(; dict) && if dict === num_dict end => begin
            mwb.num_dict = ACDict{T}()
        end
        _ => nothing
    end
    den = Mul{T}(den_coeff[], den_dict; type = eltype(type))
    @match den begin
        BSImpl.AddMul(; dict) && if dict === den_dict end => begin
            mwb.den_dict = ACDict{T}()
        end
        _ => nothing
    end

    result = Div{T}(num, den, false; type = eltype(type))
    if !isempty(arrterms)
        new_arrterms = ArgsT{T}()
        if !_isone(result)
            push!(new_arrterms, result)
        end
        fterm, rest = Iterators.peel(arrterms)
        push!(new_arrterms, fterm)
        for arrterm in rest
            prev = last(new_arrterms)
            termbase, termexp = _as_base_exp(arrterm)
            prevbase, prevexp = _as_base_exp(prev)
            if isequal(termbase, prevbase)
                new_arrterms[end] = Term{T}(^, ArgsT{T}((termbase, prevexp + termexp)); type, shape = newshape)
            else
                push!(new_arrterms, arrterm)
            end
        end
        if length(new_arrterms) == 1
            result = new_arrterms[1]
        else
            result = Term{T}(*, new_arrterms; type, shape = newshape)
        end
    end
    return result
end

mul_worker(::Type{SymReal}, terms) = SYMREAL_MULBUFFER[](terms)
mul_worker(::Type{SafeReal}, terms) = SAFEREAL_MULBUFFER[](terms)

function *(x::T...) where {T <: NonTreeSym}
    mul_worker(vartype(T), x)
end

function *(a::Union{Number, Array{<:Number}}, b::T, bs::T...) where {T <: NonTreeSym}
    return mul_worker(vartype(T), (a, b, bs...))
end

function *(a::T, b::Union{Number, Array{<:Number}}, bs::T...) where {T <: NonTreeSym}
    return mul_worker(vartype(T), (a, b, bs...))
end

###
### Div
###

@noinline function throw_bad_div_shape(x, y)
    throw(ArgumentError("""
    Arguments have invalid shapes for division - found shapes $x and $y.
    """))
end

@noinline function throw_vecdiv(x, y)
    throw(ArgumentError("""
    When dividing a vector, the denominator must be a scalar, vector or column matrix. \
    Found arguments with shapes $x and $y.
    """))
end

@noinline function throw_scalardiv(x, y)
    throw(ArgumentError("""
    When dividing a scalar, the denominator must be a scalar or vector. Found arguments \
    with shapes $x and $y.
    """))
end

# S = Scalar, * = Any, V = Vector, M = Matrix
# * / S -> *
# S / V -> (1, length(B))
# S / M -> ERR
# V / V -> (length(A), length(B))
# V / M -> (length(A), size(B, 1))    ; size(B, 2) == 1
# M / V -> ERR
# M / M -> (size(A, 1), size(B, 1))   ; size(A, 2) == size(B, 2)
function promote_shape(::typeof(/), sha::ShapeT, shb::ShapeT)
    @nospecialize sha shb
    ndims_a = _ndims_from_shape(sha)
    ndims_b = _ndims_from_shape(shb)
    if sha isa Unknown && shb isa Unknown
        ndims_a <= 2 || throw_bad_div_shape(sha, shb)
        ndims_b <= 2 || throw_bad_div_shape(sha, shb)
        ndims_a != 2 || ndims_b != 1 || throw_bad_dims(sha, shb)
        # either we get a matrix or the operation errors
        return Unknown(2)
    elseif sha isa Unknown && shb isa ShapeVecT
        ndims_b == 0 && return sha
        ndims_a <= 2 || throw_bad_div_shape(sha, shb)
        ndims_b <= 2 || throw_bad_div_shape(sha, shb)
        ndims_a != 1 || (ndims_b == 1 || length(shb[2]) == 1) || throw_vecdiv(sha, shb)
        ndims_a != 2 || ndims_b != 1 || throw_bad_dims(sha, shb)
        return Unknown(2)
    elseif sha isa ShapeVecT && shb isa Unknown
        ndims_a <= 2 || throw_bad_div_shape(sha, shb)
        ndims_b <= 2 || throw_bad_div_shape(sha, shb)
        ndims_a != 0 || ndims_b <= 1 || throw_scalardiv(sha, shb)
        ndims_a != 2 || ndims_b != 1 || throw_bad_dims(sha, shb)
        return Unknown(2)
    elseif sha isa ShapeVecT && shb isa ShapeVecT
        ndims_b == 0 && return sha
        ndims_a <= 2 || throw_bad_div_shape(sha, shb)
        ndims_b <= 2 || throw_bad_div_shape(sha, shb)
        if ndims_a == 0
            ndims_b == 1 && return ShapeVecT((1:1, shb[1]))
            throw_scalardiv(sha, shb)
        elseif ndims_a == 1
            ndims_b == 1 || length(shb[2]) == 1 || throw_vecdiv(sha, shb)
            return ShapeVecT((sha[1], shb[1]))
        else
            # ndims_a == 2
            ndims_b == 1 && throw_bad_div_shape(sha, shb)
            length(sha[2]) == length(shb[2]) || throw_bad_div_shape(sha, shb)
            return ShapeVecT((sha[1], shb[1]))
        end
    end
    _unreachable()
end

function _fslash_worker(::Type{T}, a, b) where {T}
    if !_numeric_or_arrnumeric_symtype(a) || !_numeric_or_arrnumeric_symtype(b)
        throw(MethodError(/, (a, b)))
    end
    if isconst(a) || isconst(b)
        return Const{T}(unwrap_const(a) / unwrap_const(b))
    end
    type = promote_symtype(/, symtype(a), symtype(b))
    newshape = promote_shape(/, shape(a), shape(b))
    Div{T}(a, b, false; type, shape = newshape)
end

function /(a::Union{S,Number,AbstractArray{<:Number}}, b::S) where {S <: NonTreeSym}
    _fslash_worker(vartype(S), a, b)
end

function /(a::S, b::Union{Number,AbstractArray{<:Number}}) where {S <: NonTreeSym}
    _fslash_worker(vartype(S), a, b)
end

function //(a::Union{S,Number,AbstractArray{<:Number}}, b::S) where {S <: NonTreeSym}
    if !_rational_or_arrrational_symtype(a) || !_rational_or_arrrational_symtype(b)
        throw(MethodError(//, (a, b)))
    end
    _fslash_worker(vartype(S), a, b)
end

function //(a::S, b::Union{Number,AbstractArray{<:Number}}) where {S <: NonTreeSym}
    if !_rational_or_arrrational_symtype(a) || !_rational_or_arrrational_symtype(b)
        throw(MethodError(//, (a, b)))
    end
    _fslash_worker(vartype(S), a, b)
end

@noinline function throw_bad_dims(x, y)
    throw(ArgumentError("""
    Both arguments to \\ must have <= 2 dimensions. Found arguments with shapes $x and $y.
    """))
end

@noinline function throw_scalar_rhs(x, y)
    throw(ArgumentError("""
    The second argument to \\ cannot be a scalar if the first argument is an array. Found
    arguments with shapes $x and $y.
    """))
end

@noinline function throw_first_dim_different(x, y)
    throw(ArgumentError("""
    The length of the first dimension of both arguments to \\ must be identical. Found
    arguments with shapes $x and $y.
    """))
end

# S = Scalar, * = Any, V = Vector, M = Matrix
# S \ * -> *
# V \ S -> ERR
# V \ V -> S                        ; len(A) == len(B)
# V \ M -> (1, shape(B, 2))         ; len(A) == size(B, 1)
# M \ S -> ERR
# M \ V -> (size(A, 2))             ; size(A, 1) == length(B)
# M \ M -> (size(A, 2), size(B, 2)) ; size(A, 1) == size(B, 1)
function promote_shape(::typeof(\), sha::ShapeT, shb::ShapeT)
    @nospecialize sha shb
    ndims_a = _ndims_from_shape(sha)
    ndims_b = _ndims_from_shape(shb)
    if sha isa Unknown && shb isa Unknown
        sha.ndims <= 2 || throw_bad_dims(sha, shb)
        shb.ndims <= 2 || throw_bad_dims(sha, shb)
        sha.ndims == 0 && return Unknown(0)
        shb.ndims == 0 && return Unknown(0)
        sha.ndims == 1 && shb.ndims == 1 && return ShapeVecT()
        return shb
    elseif sha isa Unknown && shb isa ShapeVecT
        sha.ndims <= 2 || throw_bad_dims(sha, shb)
        length(shb) <= 2 || throw_bad_dims(sha, shb)
        length(shb) == 0 && throw_scalar_rhs(sha, shb)
        sha.ndims == 0 && return Unknown(0)
        sha.ndims == 1 && ndims_b == 1 && return ShapeVecT()
        sha.ndims == 1 && ndims_b == 2 && return ShapeVecT((1:1, shb[2]))
        sha.ndims == 2 && return Unknown(ndims_b)
        _unreachable()
    elseif sha isa ShapeVecT && shb isa Unknown
        shb.ndims == 0 && return Unknown(0)
        ndims_a == 0 && return shb
        ndims_a <= 2 || throw_bad_dims(sha, shb)
        shb.ndims <= 2 || throw_bad_dims(sha, shb)
        ndims_a == 1 && shb.ndims == 1 && return ShapeVecT()
        ndims_a == 1 && shb.ndims == 2 && return shb
        ndims_a == 2 && shb.ndims == 1 && return ShapeVecT((sha[1],))
        ndims_a == 2 && shb.ndims == 2 && return shb
        _unreachable()
    elseif sha isa ShapeVecT && shb isa ShapeVecT
        ndims_a == 0 && return shb
        ndims_b == 0 && throw_scalar_rhs(sha, shb)
        length(sha[1]) == length(shb[1]) || throw_first_dim_different(sha, shb)
        ndims_a <= 2 || throw_bad_dims(sha, shb)
        ndims_b <= 2 || throw_bad_dims(sha, shb)
        if ndims_a == 1 && ndims_b == 1
            return ShapeVecT()
        elseif ndims_a == 1 && ndims_b == 2
            return ShapeVecT((1:1, shb[2]))
        elseif ndims_a == 2 && ndims_b == 1
            return ShapeVecT((sha[2],))
        elseif ndims_a == 2 && ndims_b == 2
            return ShapeVecT((sha[2], shb[2]))
        end
        _unreachable()
    end
    _unreachable()
end

function _bslash_worker(::Type{T}, a, b) where {T}
    if !_numeric_or_arrnumeric_symtype(a) || !_numeric_or_arrnumeric_symtype(b)
        throw(MethodError(\, (a, b)))
    end
    if isconst(a) || isconst(b)
        return Const{T}(unwrap_const(a) \ unwrap_const(b))
    end
    sha = shape(a)
    type = promote_symtype(\, symtype(a), symtype(b))
    newshape = promote_shape(\, shape(a), shape(b))
    if _is_array_shape(newshape) || _is_array_shape(sha)
        # Scalar \ Anything == Anything / Scalar
        return Term{T}(\, ArgsT{T}((a, b)); type, shape = newshape)
    else
        return Div{T}(b, a, false; type, shape = newshape)
    end
end

function \(a::Union{S,Number,AbstractArray{<:Number}}, b::S) where {S <: NonTreeSym}
    _bslash_worker(vartype(S), a, b)
end
function \(a::T, b::Union{Number, <:AbstractArray{<:Number}}) where {T <: NonTreeSym}
    _bslash_worker(vartype(T), a, b)
end

###
### Pow
###

@noinline function throw_matmatpow(x, y)
    throw(ArgumentError("""
    Cannot raise matrix to matrix power - tried to raise array of shape $x to array of \
    shape $y.
    """))
end

@noinline function throw_nonmatbase(x)
    throw(ArgumentError("""
    Matrices are the only arrays that can be raised to a power. Found array of shape $x.
    """))
end

@noinline function throw_nonmatexp(x)
    throw(ArgumentError("""
    Matrices are the only arrays that can be an exponent. Found array of shape $x.
    """))
end

@noinline function throw_nonsquarebase(x)
    throw(ArgumentError("""
    Only square matrices can be raised to a power. Found array of shape $x.
    """))
end

@noinline function throw_nonsquareexp(x)
    throw(ArgumentError("""
    Only a square matrix can be an exponent. Found array of shape $x.
    """))
end

function promote_shape(::typeof(^), sh1::ShapeT, sh2::ShapeT)
    @nospecialize sh1 sh2
    if sh1 isa Unknown && sh2 isa Unknown
        throw_matmatpow(sh1, sh2)
    elseif sh1 isa Unknown && sh2 isa ShapeVecT
        isempty(sh2) || throw_matmatpow(sh1, sh2)
        sh1.ndims == 2 || sh1.ndims == 0 || throw_nonmatbase(sh1)
        return Unknown(2) # either the result is a matrix or the operation will error
    elseif sh1 isa ShapeVecT && sh2 isa Unknown
        isempty(sh1) || throw_matmatpow(sh1, sh2)
        sh2.ndims == 2 || sh2.ndims == 0 || throw_nonmatexp(sh2)
        return Unknown(2) # either the result is a matrix or the operation will error
    elseif sh1 isa ShapeVecT && sh2 isa ShapeVecT
        if isempty(sh1) && isempty(sh2)
            return sh1
        elseif isempty(sh1)
            length(sh2) == 2 || throw_nonmatexp(sh2)
            length(sh2[1]) == length(sh2[2]) || throw_nonsquareexp(sh2)
            return sh2
        elseif isempty(sh2)
            length(sh1) == 2 || throw_nonmatbase(sh1)
            length(sh1[1]) == length(sh1[2]) || throw_nonsquarebase(sh1)
            return sh1
        else
            throw_matmatpow(sh1, sh2)
        end
    end
end

function ^(a::BasicSymbolic{T}, b) where {T <: Union{SymReal, SafeReal}}
    if !_numeric_or_arrnumeric_symtype(a) || !_numeric_or_arrnumeric_symtype(b)
        throw(MethodError(^, (a, b)))
    end
    isconst(a) && return Const{T}(^(unwrap_const(a), b))
    b = unwrap_const(unwrap(b))
    sha = shape(a)
    shb = shape(b)
    newshape = promote_shape(^, sha, shb)
    type = promote_symtype(^, symtype(a), symtype(b))

    if _is_array_shape(sha)
        @match a begin
            BSImpl.Term(; f, args) && if f === (^) && isconst(args[1]) end => begin
                base, exp = args
                return Term{T}(^, ArgsT{T}((base, exp * b)); type, shape = newshape)
            end
            BSImpl.Term(; f) && if f === (*) end => begin
                coeff, rest = _split_arrterm_scalar_coeff(a)
                if _isone(coeff)
                    return Term{T}(^, ArgsT{T}((rest, Const{T}(b))); type, shape = newshape)
                end
                return coeff ^ b * rest ^ b
            end
            _ => return Term{T}(^, ArgsT{T}((a, Const{T}(b))); type, shape = newshape)
        end
    elseif _is_array_shape(shb)
        return Term{T}(^, ArgsT{T}((a, Const{T}(b))); type, shape = newshape)
    end
    if b isa Number
        iszero(b) && return Const{T}(1)
        isone(b) && return Const{T}(a)
    end
    if b isa Real && b < 0
        return Div{T}(1, a ^ (-b), false; type)
    end
    if b isa Number && iscall(a) && operation(a) === (^) && isconst(arguments(a)[2]) && symtype(arguments(a)[2]) <: Number
        base, exp = arguments(a)
        exp = unwrap_const(exp)
        return Const{T}(base ^ (exp * b))
    end
    @match a begin
        BSImpl.Div(; num, den) => return BSImpl.Div{T}(num ^ b, den ^ b, false; type)
        _ => nothing
    end
    if b isa Number
        @match a begin
            BSImpl.AddMul(; coeff, dict, variant, shape, type) && if variant == AddMulVariant.MUL end => begin
                if coeff isa Real && coeff < 0 && !isinteger(b)
                    coeff = (-coeff) ^ b
                    newmul = BSImpl.AddMul{T}(1, dict, variant; shape, type)
                    newpow = Term{T}(^, ArgsT{T}((newmul, b)); shape, type)
                    return mul_worker(T, (coeff, newpow))
                else
                    coeff = coeff ^ b
                    dict = copy(dict)
                    map!(Base.Fix1(*, b), values(dict))
                    return BSImpl.AddMul{T}(coeff, dict, variant; shape, type)
                end
            end
            _ => nothing
        end
    end
    return BSImpl.Term{T}(^, ArgsT{T}((a, Const{T}(b))); type)
end

function ^(a::Union{Number, Matrix{<:Number}}, b::BasicSymbolic{T}) where {T}
    _numeric_or_arrnumeric_symtype(b) || throw(MethodError(^, (a, b)))
    newshape = promote_shape(^, shape(a), shape(b))
    type = promote_symtype(^, symtype(a), symtype(b))
    if _is_array_shape(newshape) && _isone(a)
        if newshape isa Unknown
            return Const{T}(LinearAlgebra.I)
        else
            return Const{T}(LinearAlgebra.I(length(newshape[1])))
        end
    end
    Term{T}(^, ArgsT{T}((Const{T}(a), b)); type, shape = newshape)
end

@inline _indexed_ndims() = 0
@inline _indexed_ndims(::Type{T}, rest...) where {T <: Integer} = _indexed_ndims(rest...)
@inline _indexed_ndims(::Type{T}, rest...) where {eT <: Integer, T <: AbstractVector{eT}} = 1 + _indexed_ndims(rest...)
@inline _indexed_ndims(::Type{Colon}, rest...) = 1 + _indexed_ndims(rest...)
@inline _indexed_ndims(::Type{T}, rest...) where {T} = throw(ArgumentError("Invalid index type $T."))

function promote_symtype(::typeof(getindex), ::Type{T}, Ts::Vararg{Any, N}) where {N, eT, T <: AbstractArray{eT, N}}
    nD = _indexed_ndims(Ts...)
    nD == 0 ? eT : Array{eT, nD}
end

function promote_symtype(::typeof(getindex), ::Type{T}, Ts...) where {T}
    throw(ArgumentError("Symbolic `getindex` requires cartesian indexing."))
end

@noinline function throw_no_unknown_colon()
    throw(ArgumentError("Cannot index array of unknown shape with `Colon` (`:`)."))
end

@noinline function throw_index_larger_than_shape(i, ii, shi)
    throw(ArgumentError("""
    Tried to index array whose `$i`th dimension has shape $shi with index $ii.
    """))
end

@noinline function throw_not_array(x)
    throw(ArgumentError("""
    Cannot call `getindex` on non-array symbolics - found array of shape $x.
    """))
end

function promote_shape(::typeof(getindex), sharr::ShapeT, shidxs::ShapeVecT...)
    @nospecialize sharr
    # `promote_symtype` rules out the presence of multidimensional indices - each index
    # is either an integer, Colon or vector of integers.
    _is_array_shape(sharr) || throw_not_array(sharr)
    result = ShapeVecT()
    for (i, idx) in enumerate(shidxs)
        isempty(idx) && continue
        idx[1] == 1:0 && sharr isa Unknown && throw_no_unknown_colon()
        ii = idx[1] == 1:0 ? sharr[i] : 1:length(idx[1])
        push!(result, ii)
        if sharr isa ShapeVecT && length(ii) > length(sharr[i])
            throw_index_larger_than_shape(i, ii, sharr[i])
        end
    end

    return result
end

function promote_shape(::typeof(getindex), sharr::ShapeT, shidxs::ShapeT...)
    throw(ArgumentError("Cannot use arrays of unknown size for indexing."))
end

function Base.getindex(arr::BasicSymbolic{T}, idxs::Union{BasicSymbolic{T}, Int, AbstractArray{<:Integer}, Colon}...) where {T}
    type = promote_symtype(getindex, symtype(arr), symtype.(idxs)...)
    newshape = promote_shape(getindex, shape(arr), shape.(idxs)...)
    return BSImpl.Term{T}(getindex, ArgsT{T}((arr, Const{T}.(idxs)...)); type, shape = newshape)
end
