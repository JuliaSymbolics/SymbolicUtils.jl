export SymReal, SafeReal, TreeReal, vartype

abstract type SymVariant end
"""
    $TYPEDEF

One of three possible values of the [`vartype`](@ref). This variant is the default and
behaves as a typical ideal scalar algebra would be expected to.
"""
abstract type SymReal <: SymVariant end
"""
    $TYPEDEF

One of three possible values of the [`vartype`](@ref). This variant is identical to
[`SymReal`](@ref) except common terms in the numerator and denominator of a division are
not cancelled out.
"""
abstract type SafeReal <: SymVariant end
"""
    $TYPEDEF

One of three possible values of the [`vartype`](@ref). This variant does not assume anything
about the algebra and always uses the default tree form for expressions.
"""
abstract type TreeReal <: SymVariant end

###
### Uni-type design
###

# Unknown(-1) is an array of unknown ndims
# Empty ShapeVecT is a scalar
"""
    $TYPEDEF

A struct used as the `shape` of symbolic expressions with unknown size.

# Fields

$TYPEDFIELDS
"""
struct Unknown
    """
    An integer >= -1 indicating the number of dimensions of the symbolic expression of
    unknown size. A value of `-1` indicates the number of dimensions is also unknown.
    """
    ndims::Int

    function Unknown(x::Int)
        x >= -1 || throw(ArgumentError("Unknown ndims must be -1."))
        new(x)
    end
end

const SCALARS = [Bool, Int, Int32, BigInt, Float64, Float32, BigFloat, Rational{Int}, Rational{Int32}, Rational{BigInt}, ComplexF32, ComplexF64, Complex{BigFloat}]

"""
    $TYPEDEF

Type of metadata field for symbolics.
"""
const MetadataT = Union{Base.ImmutableDict{DataType, Any}, Nothing}
"""
    $TYPEDEF

A custom vector type which does not allocate for small numbers of elements. If the number of elements is
known at compile time, it should be passed as a `Tuple` to the constructor.
"""
const SmallV{T} = SmallVec{T, Vector{T}}
const ShapeVecT = SmallV{UnitRange{Int}}
"""
    $TYPEDEF

Type that represents the [`SymbolicUtils.shape`](@ref) of symbolics.
"""
const ShapeT = Union{Unknown, ShapeVecT}
const IdentT = Union{IDType, Nothing}
const MonomialOrder = MP.Graded{MP.Reverse{MP.InverseLexOrder}}
const PolyVarOrder = DP.Commutative{DP.CreationOrder}
const ExamplePolyVar = only(DP.@polyvar __DUMMY__ monomial_order=MonomialOrder)
const PolyVarT = typeof(ExamplePolyVar)
const PolyCoeffT = Number
const _PolynomialT{T} = DP.Polynomial{PolyVarOrder, MonomialOrder, T}
# we can't actually print a zero polynomial of this type, since it attempts to call
# `zero(Any)` but that doesn't matter because we shouldn't ever store a zero polynomial
const PolynomialT = _PolynomialT{PolyCoeffT}
"""
    $TYPEDEF

Allowed types for the [`SymbolicUtils.symtype`](@ref) of symbolics.
"""
const TypeT = DataType
const MonomialT = DP.Monomial{PolyVarOrder, MonomialOrder}
const MonomialVecT = DP.MonomialVector{PolyVarOrder, MonomialOrder}

"""
    $TYPEDSIGNATURES

Create a zero polynomial with empty monomial vector.

# Returns
- A `PolynomialT` representing the zero polynomial
"""
function zeropoly()
    mv = DP.MonomialVector{PolyVarOrder, MonomialOrder}()
    PolynomialT(PolyCoeffT[], mv)
end

"""
    $TYPEDSIGNATURES

Create a polynomial representing the constant 1.

# Returns
- A `PolynomialT` representing the constant polynomial 1 with an empty monomial vector
"""
function onepoly()
    V = DP.Commutative{DP.CreationOrder}
    mv = DP.MonomialVector{V, MonomialOrder}(DP.Variable{V, MonomialOrder}[], [Int[]])
    PolynomialT(PolyCoeffT[1], mv)
end

"""
    $(TYPEDEF)

An EnumX.jl enum used to distinguish between addition and multiplication in
[`SymbolicUtils.BSImpl.AddMul`](@ref).
"""
@enumx AddMulVariant::Bool begin
    ADD
    MUL
end

"""
    $(TYPEDEF)

Core ADT for symbolic expressions.
"""
@data mutable BasicSymbolicImpl{T <: SymVariant} begin 
    struct Const
        const val::Any
        hash::UInt
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
    struct ArrayOp
        # The indices on the LHS of the einsum. Either an `Int` for a reduced yet
        # uncollapsed dimension (e.g. `prod(x; dims = 1)` generates `[1, i]`) or
        # a symbolic idx. We avoid Const since it stores the value as `::Any`.
        const output_idx::SmallV{Union{Int, BasicSymbolicImpl.Type{T}}}
        # The expression on the RHS of the einsum. Uses the indices in `output_idx`
        const expr::BasicSymbolicImpl.Type{T}
        # The reduction function for reduced dimensions
        const reduce::Any
        # The operation expressed as a function of array arguments. Takes preference
        # in codegen. E.g. if this is `x * y` codegen will generate `x * y` instead
        # of writing the matmul with loops.
        const term::Union{BasicSymbolicImpl.Type{T}, Nothing}
        # Optional map from symbolic indices in `output_idx` to the range they can
        # take. Any index not present in this takes its full range of values.
        const ranges::Dict{BasicSymbolicImpl.Type{T}, StepRange{Int, Int}}
        const metadata::MetadataT
        const shape::ShapeT
        const type::TypeT
        const args::SmallV{BasicSymbolicImpl.Type{T}}
        hash::UInt
        hash2::UInt
        id::IdentT
    end
end

"""
    Alias for `SymbolicUtils.BasicSymbolicImpl`.
"""
const BSImpl = BasicSymbolicImpl
"""
    Alias for `SymbolicUtils.BasicSymbolicImpl.Type`.
"""
const BasicSymbolic = BSImpl.Type
"""
    The type of a mutable buffer containing symbolic arguments. Passing this to the
    [`SymbolicUtils.Term`](@ref) constructor will avoid allocating a new array.
"""
const ArgsT{T} = SmallV{BasicSymbolic{T}}
"""
    The type of a read-only buffer containing symbolic arguments. Passing this to the
    [`SymbolicUtils.Term`](@ref) constructor will avoid allocating a new array. This is
    the type returned from [`TermInterface.arguments`](@ref).
"""
const ROArgsT{T} = ReadOnlyVector{BasicSymbolic{T}, ArgsT{T}}
"""
    The type of the dictionary stored in [`BSImpl.AddMul`](@ref). Passing this to the
    [`SymbolicUtils.Add`](@ref) or [`SymbolicUtils.Mul`](@ref) constructors will avoid
    allocating a new dictionary.
"""
const ACDict{T} = Dict{BasicSymbolic{T}, Number}
"""
    The type of the `output_idxs` field in [`BSImpl.ArrayOp`](@ref).
"""
const OutIdxT{T} = SmallV{Union{Int, BasicSymbolic{T}}}
"""
    The type of the `ranges` field in [`BSImpl.ArrayOp`](@ref).
"""
const RangesT{T} = Dict{BasicSymbolic{T}, StepRange{Int, Int}}

"""
    $TYPEDSIGNATURES

Return the Julia type that the given symbolic expression `x` represents.
Can also be called on non-symbolic values, in which case it is equivalent to
`typeof`.
"""
function symtype(x::BasicSymbolic)
    # use `@match` instead of `x.type` since it is faster
    @match x begin
        BSImpl.Const(; val) => typeof(val)
        BSImpl.Sym(; type) => type
        BSImpl.Term(; type) => type
        BSImpl.AddMul(; type) => type
        BSImpl.Div(; type) => type
        BSImpl.ArrayOp(; type) => type
    end
end
symtype(x) = typeof(x)

"""
    $METHODLIST

Extract the variant type of a `BasicSymbolic`.
"""
vartype(x::BasicSymbolic{T}) where {T} = T
vartype(::Type{BasicSymbolic{T}}) where {T} = T

"""
    shape(x)

Get the shape of a value or symbolic expression. Generally equivalent to `axes` for
non-symbolic `x`, but also works on non-array values.
"""
function shape end

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
    push!(cur_expr.args, :(x isa $(Colon)))
    push!(cur_expr.args, :($shape($Colon())))
    new_expr = Expr(:elseif)
    push!(cur_expr.args, new_expr)
    cur_expr = new_expr

    push!(cur_expr.args, :(x isa $(LinearAlgebra.UniformScaling)))
    push!(cur_expr.args, Unknown(2))
    new_expr = Expr(:elseif)
    push!(cur_expr.args, new_expr)
    cur_expr = new_expr

    push!(cur_expr.args, :(x isa $(Number)))
    push!(cur_expr.args, ShapeVecT())
    new_expr = Expr(:elseif)
    push!(cur_expr.args, new_expr)
    cur_expr = new_expr

    push!(cur_expr.args, :(x isa $(AbstractArray)))
    push!(cur_expr.args, :($ShapeVecT(axes(x))))
    push!(cur_expr.args, :($ShapeVecT()))
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
        BSImpl.ArrayOp(; shape) => shape
    end
end

shape(x) = _shape_notsymbolic(x)::ShapeT
shape(::Colon) = ShapeVecT((1:0,))

function SymbolicIndexingInterface.symbolic_type(x::BasicSymbolic)
    symtype(x) <: AbstractArray ? ArraySymbolic() : ScalarSymbolic()
end
SymbolicIndexingInterface.symbolic_type(::Type{BasicSymbolic}) = ScalarSymbolic()
SymbolicIndexingInterface.symbolic_type(::Type{BasicSymbolic{T}}) where {T} = ScalarSymbolic()

function SymbolicIndexingInterface.getname(x::BasicSymbolic{T}) where {T}
    @match x begin
        BSImpl.Sym(; name) => name
        BSImpl.Term(; f, args) && if f === getindex end => getname(args[1])
        BSImpl.Term(; f) && if f isa BasicSymbolic{T} end => getname(f)
    end
end

function SymbolicIndexingInterface.hasname(x::BasicSymbolic{T}) where {T}
    @match x begin
        BSImpl.Sym(;) => true
        BSImpl.Term(; f) && if f === getindex || f isa BasicSymbolic{T} end => true
        _ => false
    end
end

"""
    $(TYPEDSIGNATURES)

Return the inner `Symbolic` wrapped in a non-symbolic subtype. Defaults to
returning the input as-is.
"""
unwrap(@nospecialize(x)) = x

"""
    $(TYPEDSIGNATURES)

Properties of `obj` that override any explicitly provided values in
`ConstructionBase.setproperties`.
"""
override_properties(obj::BSImpl.Type) = override_properties(MData.variant_type(obj))

function override_properties(obj::Type{<:BSImpl.Variant})
    @match obj begin
        ::Type{<:BSImpl.Const} => (; id = nothing, hash = 0)
        ::Type{<:BSImpl.Sym} => (; id = nothing, hash = 0, hash2 = 0)
        ::Type{<:BSImpl.AddMul} => (; id = nothing, hash = 0, hash2 = 0)
        ::Type{<:BSImpl.Term} => (; id = nothing, hash = 0, hash2 = 0)
        ::Type{<:BSImpl.Div} => (; id = nothing, hash = 0, hash2 = 0)
        ::Type{<:BSImpl.ArrayOp} => (; id = nothing, hash = 0, hash2 = 0)
    end
end

ordered_override_properties(::Type{<:BSImpl.Const}) = (0, nothing,)
ordered_override_properties(::Type{<:BSImpl.Sym}) = (0, 0, nothing)
ordered_override_properties(::Type{<:BSImpl.Term}) = (0, 0, nothing)
ordered_override_properties(::Type{BSImpl.AddMul{T}}) where {T} = (ArgsT{T}(), 0, 0, nothing)
ordered_override_properties(::Type{<:BSImpl.Div}) = (0, 0, nothing)
ordered_override_properties(::Type{<:BSImpl.ArrayOp{T}}) where {T} = (ArgsT{T}(), 0, 0, nothing)

function ConstructionBase.getproperties(obj::BSImpl.Type)
    @match obj begin
        BSImpl.Const(; val, hash, id) => (; val, hash, id)
        BSImpl.Sym(; name, metadata, hash, hash2, shape, type, id) => (; name, metadata, hash, hash2, shape, type, id)
        BSImpl.Term(; f, args, metadata, hash, hash2, shape, type, id) => (; f, args, metadata, hash, hash2, shape, type, id)
        BSImpl.AddMul(; coeff, dict, variant, metadata, shape, type, args, hash, hash2, id) => (; coeff, dict, variant, metadata, shape, type, args, hash, hash2, id)
        BSImpl.Div(; num, den, simplified, metadata, hash, hash2, shape, type, id) => (; num, den, simplified, metadata, hash, hash2, shape, type, id)
        BSImpl.ArrayOp(; output_idx, expr, reduce, term, ranges, metadata, shape, type, args, hash, hash2, id) => (; output_idx, expr, reduce, term, ranges, metadata, shape, type, args, hash, hash2, id)
    end
end

function ConstructionBase.setproperties(obj::BSImpl.Type{T}, patch::NamedTuple) where {T}
    props = getproperties(obj)
    overrides = override_properties(obj)
    # We only want to invalidate `args` if we're updating `coeff` or `dict`.
    if isaddmul(obj) || isarrayop(obj)
        extras = (; args = ArgsT{T}())
    else
        extras = (;)
    end
    hashcons(MData.variant_type(obj)(; props..., patch..., overrides..., extras...)::BasicSymbolic{T})
end

"""
    $TYPEDSIGNATURES

Check if a value is a `Const` variant of `BasicSymbolic`.

# Arguments
- `x`: Value to check (for `BasicSymbolic` input returns true if `Const`, for others returns false)

# Returns
- `true` if `x` is a `BasicSymbolic` with `Const` variant, `false` otherwise
"""
isconst(x::BSImpl.Type) = MData.isa_variant(x, BSImpl.Const)

"""
    $TYPEDSIGNATURES

Check if a value is a `Sym` variant of `BasicSymbolic`.

# Arguments
- `x`: Value to check (for `BasicSymbolic` input returns true if `Sym`, for others returns false)

# Returns
- `true` if `x` is a `BasicSymbolic` with `Sym` variant, `false` otherwise
"""
issym(x::BSImpl.Type) = MData.isa_variant(x, BSImpl.Sym)

"""
    $TYPEDSIGNATURES

Check if a value is a `Term` variant of `BasicSymbolic`.

# Arguments
- `x`: Value to check (for `BasicSymbolic` input returns true if `Term`, for others returns false)

# Returns
- `true` if `x` is a `BasicSymbolic` with `Term` variant, `false` otherwise
"""
isterm(x::BSImpl.Type) = MData.isa_variant(x, BSImpl.Term)

"""
    $TYPEDSIGNATURES

Check if a value is an `AddMul` variant of `BasicSymbolic`.

# Arguments
- `x`: Value to check (for `BasicSymbolic` input returns true if `AddMul`, for others returns false)

# Returns
- `true` if `x` is a `BasicSymbolic` with `AddMul` variant, `false` otherwise
"""
isaddmul(x::BSImpl.Type) = MData.isa_variant(x, BSImpl.AddMul)

"""
    $TYPEDSIGNATURES

Check if a value is an addition (`AddMul` with ADD variant).

# Arguments
- `x`: Value to check (for `BasicSymbolic` input returns true if addition, for others returns false)

# Returns
- `true` if `x` is an `AddMul` with `ADD` variant, `false` otherwise
"""
isadd(x::BSImpl.Type) = isaddmul(x) && MData.variant_getfield(x, BSImpl.AddMul, :variant) == AddMulVariant.ADD

"""
    $TYPEDSIGNATURES

Check if a value is a multiplication (`AddMul` with MUL variant).

# Arguments
- `x`: Value to check (for `BasicSymbolic` input returns true if multiplication, for others returns false)

# Returns
- `true` if `x` is an `AddMul` with `MUL` variant, `false` otherwise
"""
ismul(x::BSImpl.Type) = isaddmul(x) && MData.variant_getfield(x, BSImpl.AddMul, :variant) == AddMulVariant.MUL

"""
    $TYPEDSIGNATURES

Check if a value is a `Div` variant of `BasicSymbolic`.

# Arguments
- `x`: Value to check (for `BasicSymbolic` input returns true if `Div`, for others returns false)

# Returns
- `true` if `x` is a `BasicSymbolic` with `Div` variant, `false` otherwise
"""
isdiv(x::BSImpl.Type) = MData.isa_variant(x, BSImpl.Div)

"""
    $TYPEDSIGNATURES

Check if a value is a power expression (`Term` with `^` operation).

# Arguments
- `x`: Value to check (for `BasicSymbolic` input returns true if power, for others returns false)

# Returns
- `true` if `x` is a `Term` with exponentiation operation, `false` otherwise

# Details
Power expressions are `Term` variants where the operation is `^` (6 uses).
"""
ispow(x::BSImpl.Type) = isterm(x) && operation(x) === (^)

"""
    $TYPEDSIGNATURES

Check if a value is an `ArrayOp` variant of `BasicSymbolic`.

# Arguments
- `x`: Value to check (for `BasicSymbolic` input returns true if `ArrayOp`, for others returns false).

# Returns
- `true` if `x` is a `BasicSymbolic` with `ArrayOp` variant, `false` otherwise.

# Details
Array operations represent vectorized computations created by the `@arrayop` macro.
"""
isarrayop(x::BSImpl.Type) = MData.isa_variant(x, BSImpl.ArrayOp)

for fname in [:isconst, :issym, :isterm, :isaddmul, :isadd, :ismul, :isdiv, :ispow, :isarrayop]
    @eval $fname(x) = false
end

###
### Base interface
###

"""
    $TYPEDSIGNATURES

Return `one(symtype(s))`
"""
Base.one( s::BSImpl.Type) = one( symtype(s))
"""
    $TYPEDSIGNATURES

Return a `Const` symbolic wrapping `1`.
"""
Base.one(::Type{BSImpl.Type{T}}) where {T} = one_of_vartype(T)
Base.oneunit(::Type{BSImpl.Type{T}}) where {T} = one_of_vartype(T)
"""
    $TYPEDSIGNATURES

Return `zero(symtype(s))`
"""
Base.zero(s::BSImpl.Type) = zero(symtype(s))
"""
    $TYPEDSIGNATURES

Return a `Const` symbolic wrapping `0`.
"""
Base.zero(::Type{BSImpl.Type{T}}) where {T} = zero_of_vartype(T)

function _name_as_operator(x::BasicSymbolic)
    @match x begin
        BSImpl.Sym(; name) => name
        BSImpl.Term(; f) => _name_as_operator(f)
        _ => _name_as_operator(operation(x))
    end
end
_name_as_operator(x) = nameof(x)

"""
    Base.nameof(s::BasicSymbolic)

Return the name of a symbolic variable. Valid only if `issym(s)`.
"""
Base.nameof(s::BasicSymbolic) = issym(s) ? s.name : error("Non-Sym BasicSymbolic doesn't have a name")

Base.convert(::Type{B}, x) where {R, B <: BasicSymbolic{R}} = BSImpl.Const{R}(unwrap(x))
Base.convert(::Type{B}, x::B) where {R, B <: BasicSymbolic{R}} = x

###
### Utilities
###

"""
    $TYPEDSIGNATURES

Extract the numeric coefficient from a multiplication expression.

# Arguments
- `x`: A symbolic expression that must be a multiplication

# Returns
- The numeric coefficient of the multiplication

# Details
This function extracts the leading numeric coefficient from a multiplication expression.
For `Term` variants, it recursively searches for nested multiplications. For `AddMul`
variants with `MUL` operation, it returns the stored coefficient. Throws an error if
the input is not a multiplication expression.
"""
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

"""
    $TYPEDSIGNATURES

Extract the constant value from a `Const` variant, or return the input unchanged.

# Arguments
- `x`: Any value, potentially a `BasicSymbolic` with a `Const` variant

# Returns
- The wrapped constant value if `x` is a `Const` variant of `BasicSymbolic`
- The input `x` unchanged otherwise

# Details
This function unwraps constant symbolic expressions to their underlying values. It handles
all three symbolic variants (`SymReal`, `SafeReal`, `TreeReal`). For non-`Const` symbolic
expressions or non-symbolic values, returns the input unchanged.
"""
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
    term(f, args...; vartype = SymReal, type = promote_symtype(f, symtype.(args)...), shape = promote_shape(f, SymbolicUtils.shape.(args)...))

Create a symbolic term with operation `f` and arguments `args`.

# Arguments
- `f`: The operation or function head of the term
- `args...`: The arguments to the operation
- `vartype`: The variant type for the term (default: `SymReal`)
- `type`: The symbolic type of the term. If not provided, it is inferred using `promote_symtype` on the function and argument types.
- `shape`: The shape of the term. If not provided, it is inferred using `promote_shape` on the function and argument shapes.

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
function term(f, args...; vartype = SymReal, type = promote_symtype(f, symtype.(args)...), shape = promote_shape(f, SymbolicUtils.shape.(args)...))
    @nospecialize f
    Term{vartype}(f, args; type, shape)
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
    md === nothing && return default
    return get(md, ctx, default)
end

# pirated for Setfield purposes:
using Base: ImmutableDict
Base.ImmutableDict(d::ImmutableDict{K,V}, x, y)  where {K, V} = ImmutableDict{K,V}(d, x, y)

assocmeta(d::Dict, ctx, val) = (d=copy(d); d[ctx] = val; d)
function assocmeta(d::Base.ImmutableDict{DataType, Any}, @nospecialize(ctx::DataType), @nospecialize(val))::ImmutableDict{DataType,Any}
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
function setmetadata(s::BasicSymbolic, @nospecialize(ctx::DataType), @nospecialize(val))
    meta = metadata(s)
    if meta isa Base.ImmutableDict{DataType, Any}
        @set s.metadata = assocmeta(meta, ctx, val)
    else
        # fresh Dict
        @set s.metadata = Base.ImmutableDict{DataType, Any}(ctx, unwrap(val))
    end
end

###
### Symbolic function / type inference
###

"""
    $TYPEDSIGNATURES

The result of applying `f` to arguments of [`SymbolicUtils.symtype`](@ref) `Ts...`

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

When constructing expressions without an explicit symtype,
`promote_symtype` is used to figure out the symtype of the Term.

It is recommended that all type arguments be annotated with [`SymbolicUtils.TypeT`](@ref)
and one method be implemented for any combination of `f` and the number of arguments. For
example, one method is implemented for unary `-` and one method for binary `-`. Each method
has an `if..elseif` chain to handle possible types. Any call to `promote_type` should be
typeasserted with `::TypeT`.
"""
promote_symtype(f, Ts...) = Any

"""
    promote_shape(f, shs::ShapeT...)

The shape of the result of applying `f` to arguments of [`shape`](@ref) `shs...`.
It is recommended that implemented methods `@nospecialize` all the shape arguments.
"""
promote_shape(f, szs::ShapeT...) = Unknown(-1)

#---------------------------
#---------------------------
#### Function-like variables
#---------------------------

struct FnType{X<:Tuple,Y,Z} end

function (f::BasicSymbolic{T})(args...) where {T}
    symtype(f) <: FnType || error("Sym $f is not callable. " *
          "Use @syms $f(var1, var2,...) to create it as a callable.")
    Term{T}(f, args; type = promote_symtype(f, symtype.(args)...), shape = f.shape, metadata = f.metadata)
end

fntype_X_Y(::Type{<: FnType{X, Y}}) where {X, Y} = (X, Y)

function promote_shape(f::BasicSymbolic{T}, args::ShapeT...) where {T}
    @nospecialize args
    return shape(f)
end

"""
    $(TYPEDSIGNATURES)

Check if `x` is a symbolic representing a function (as opposed to a dependent variable).
A symbolic function either has a defined signature or the function type defined. For
example, all of the below are considered symbolic functions:

```julia
@syms f(::Real, ::Real) g(::Real)::Integer h(::Real)[1:2]::Integer (ff::MyCallableT)(..)
```

However, the following is considered a dependent variable with unspecified independent
variable:

```julia
@syms x(..)
```

See also: [`SymbolicUtils.is_function_symtype`](@ref).
"""
is_function_symbolic(x::BasicSymbolic) = is_function_symtype(symtype(x))
"""
    $(TYPEDSIGNATURES)

Check if the given `symtype` represents a function (as opposed to a dependent variable).

See also: [`SymbolicUtils.is_function_symbolic`](@ref).
"""
is_function_symtype(::Type{T}) where {T} = false
is_function_symtype(::Type{FnType{Tuple, Y, Nothing}}) where {Y} = false
is_function_symtype(::Type{FnType{X, Y, Z}}) where {X, Y, Z} = true
"""
    $(TYPEDSIGNATURES)

Check if the given symbolic `x` is the result of calling a symbolic function (as opposed
to a dependent variable).

See also: [`SymbolicUtils.is_function_symbolic`](@ref).
"""
function is_called_function_symbolic(x::BasicSymbolic{T}) where {T}
    @match x begin
        BSImpl.Term(; f) && if f isa BasicSymbolic{T} end => is_function_symbolic(f)
        _ => false
    end
end

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
