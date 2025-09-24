export SymReal, SafeReal, TreeReal, vartype

abstract type SymVariant end
abstract type SymReal <: SymVariant end
abstract type SafeReal <: SymVariant end
abstract type TreeReal <: SymVariant end

###
### Uni-type design
###

# Unknown(-1) is an array of unknown ndims
# Empty ShapeVecT is a scalar
struct Unknown
    ndims::Int

    function Unknown(x::Int)
        x >= -1 || throw(ArgumentError("Unknown ndims must be -1."))
        new(x)
    end
end

const MetadataT = Union{Base.ImmutableDict{DataType, Any}, Nothing}
const SmallV{T} = SmallVec{T, Vector{T}}
const ShapeVecT = SmallV{UnitRange{Int}}
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
const TypeT = Union{DataType, UnionAll, Union}
const MonomialT = DP.Monomial{PolyVarOrder, MonomialOrder}

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

const BSImpl = BasicSymbolicImpl
const BasicSymbolic = BSImpl.Type
const ArgsT{T} = SmallV{BasicSymbolic{T}}
const ROArgsT{T} = ReadOnlyVector{BasicSymbolic{T}, ArgsT{T}}
const ACDict{T} = Dict{BasicSymbolic{T}, Number}
const OutIdxT{T} = SmallV{Union{Int, BasicSymbolic{T}}}
const RangesT{T} = Dict{BasicSymbolic{T}, StepRange{Int, Int}}

function basicsymbolic_to_polyvar(bs_to_poly::AbstractDict, x::BasicSymbolic)::PolyVarT
    get!(bs_to_poly, x) do
        inner_name = _name_as_operator(x)
        name = Symbol(inner_name, :_, hash(x))
        MP.similar_variable(ExamplePolyVar, name)
    end
end

function subs_poly(poly, vars::AbstractVector{BasicSymbolic{T}}) where {T}
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
        BSImpl.ArrayOp(; type) => type
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
        ::Type{<:BSImpl.Const} => (; id = nothing, hash = 0)
        ::Type{<:BSImpl.Sym} => (; id = nothing, hash = 0, hash2 = 0)
        ::Type{<:BSImpl.AddMul} => (; id = nothing, hash = 0, hash2 = 0)
        ::Type{<:BSImpl.Term} => (; id = nothing, hash = 0, hash2 = 0)
        ::Type{<:BSImpl.Div} => (; id = nothing, hash = 0, hash2 = 0)
        ::Type{<:BSImpl.ArrayOp} => (; id = nothing, hash = 0, hash2 = 0)
        _ => throw(UnimplementedForVariantError(override_properties, obj))
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
@inline function TermInterface.operation(x::BSImpl.Type{T}) where {T}
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
        BSImpl.ArrayOp(; term) => begin
            if term === nothing
                ArrayOp{T}
            elseif term isa BasicSymbolic{T}
                operation(term)
            end
        end
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
        BSImpl.ArrayOp(; output_idx, expr, reduce, term, ranges, shape, type, args) => begin
            if term === nothing
                isempty(args) || return ROArgsT{T}(args)
                push!(args, Const{T}(output_idx))
                push!(args, Const{T}(expr))
                push!(args, Const{T}(reduce))
                push!(args, Const{T}(term))
                push!(args, Const{T}(ranges))
                return ROArgsT{T}(args)
            elseif term isa BasicSymbolic{T}
                return arguments(term)
            end
        end
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
isarrayop(x::BSImpl.Type) = MData.isa_variant(x, BSImpl.ArrayOp)

for fname in [:isconst, :issym, :isterm, :isaddmul, :isadd, :ismul, :isdiv, :ispow, :isarrayop]
    @eval $fname(x) = false
end

###
### Base interface
###

Base.isequal(::BasicSymbolic, x::Union{Number, AbstractArray}) = false
Base.isequal(x::Union{Number, AbstractArray}, ::BasicSymbolic) = false
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

function isequal_rangesdict(d1::RangesT{T}, d2::RangesT{T}, full) where {T}
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
        isequal(v, v2) && isequal_bsimpl(k, k2, true) || return false
    end
    return true
end

isequal_bsimpl(::BSImpl.Type, ::BSImpl.Type, ::Bool) = false

function isequal_bsimpl(a::BSImpl.Type{T}, b::BSImpl.Type{T}, full::Bool) where {T}
    a === b && return true
    ida = a.id
    idb = b.id
    ida === idb && ida !== nothing && return true

    Ta = MData.variant_type(a)
    Tb = MData.variant_type(b)
    Ta === Tb || return false

    if full && ida !== idb && ida !== nothing && idb !== nothing
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
        (BSImpl.ArrayOp(; output_idx = o1, expr = e1, reduce = f1, term = t1, ranges = r1, shape = s1, type = type1), BSImpl.ArrayOp(; output_idx = o2, expr = e2, reduce = f2, term = t2, ranges = r2, shape = s2, type = type2)) => begin
            isequal(o1, o2) && isequal(e1, e2) && isequal(f1, f2)::Bool && isequal(t1, t2) && isequal_rangesdict(r1, r2, full) && s1 == s2 && t1 === t2
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

function hash_rangesdict(d::RangesT, h::UInt, full::Bool)
    hv = Base.hasha_seed
    for (k, v) in d
        h1 = hash(v, zero(UInt))
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
        BSImpl.Const(; val, hash) => begin
            if iszero(hash)
                h = s.hash = hash_somescalar(val, h)::UInt
            end
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
            hash_bsimpl(num, hash_bsimpl(den, Base.hash(shape, Base.hash(type, h)), full), full) ⊻ DIV_SALT
        end
        BSImpl.ArrayOp(; output_idx, expr, reduce, term, ranges, shape, type, hash, hash2) => begin
            full && !iszero(hash2) && return hash2
            !full && !iszero(hash) && return hash
            Base.hash(output_idx, hash_bsimpl(expr, Base.hash(reduce, Base.hash(term, hash_rangesdict(ranges, Base.hash(shape, Base.hash(type, h)), full)))::UInt, full))
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
Base.one( ::Type{<:BSImpl.Type}) = 1
Base.zero(::Type{<:BSImpl.Type}) = 0

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
const WCS_LOCK = ReentrantLock()
const WCS = WeakCacheSet{AllBasicSymbolics}()

function generate_id()
    IDType()
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
        k = (@lock WCS_LOCK getkey!(WCS, s))::typeof(s)
        if k.id === nothing
            k.id = generate_id()
        end
        return k::typeof(s)
    end true
end

const SMALLV_DEFAULT_SYMREAL = hashcons(BSImpl.Const{SymReal}(0, 0, nothing))
const SMALLV_DEFAULT_SAFEREAL = hashcons(BSImpl.Const{SafeReal}(0, 0, nothing))
const SMALLV_DEFAULT_TREEREAL = hashcons(BSImpl.Const{TreeReal}(0, 0, nothing))

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
    meta = Base.ImmutableDict{DataType, Any}()
    for kvp in x
        meta = Base.ImmutableDict(meta, kvp)
    end
    return meta
end

default_shape(::Type{T}) where {E, N, T <: AbstractArray{E, N}} = Unknown(N)
default_shape(::Type{T}) where {T <: AbstractArray} = Unknown(-1)
default_shape(_) = ShapeVecT()

Base.convert(::Type{B}, x) where {R, B <: BasicSymbolic{R}} = BSImpl.Const{R}(unwrap(x))
Base.convert(::Type{B}, x::B) where {R, B <: BasicSymbolic{R}} = x

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
    return _dict::ACDict{T}
end

function unwrap_dict(dict)
    if any(x -> unwrap(x) !== x, keys(dict))
        typeof(dict)(unwrap(k) => v for (k, v) in dict)
    else
        dict
    end
end

function parse_output_idxs(::Type{T}, outidxs::Union{Tuple, AbstractVector}) where {T}
    outidxs isa OutIdxT{T} && return outidxs
    _outidxs = OutIdxT{T}()
    sizehint!(_outidxs, length(outidxs))
    for i in outidxs
        push!(_outidxs, unwrap_const(unwrap(i)))
    end
    return _outidxs::OutIdxT{T}
end

function parse_shape(sh)
    sh isa Unknown && return sh
    sh isa ShapeVecT && return sh
    _sh = ShapeVecT()
    for dim in sh
        push!(_sh, dim)
    end
    return _sh
end

function parse_rangedict(::Type{T}, dict::AbstractDict) where {T}
    dict isa RangesT{T} && return dict
    _dict = RangesT{T}()
    for (k, v) in dict
        _dict[unwrap_const(unwrap(k))] = unwrap_const(unwrap(v))
    end
    return _dict::RangesT{T}
end

function _is_tuple_or_array_of_symbolics(O)
    return O isa Code.CodegenPrimitive ||
        (symbolic_type(O) != NotSymbolic() && !(O isa Union{Symbol, Expr})) ||
        _is_array_of_symbolics(O) ||
        _is_tuple_of_symbolics(O)
end

function _is_array_of_symbolics(O)
    # O is an array, not a symbolic array, and either has a non-symbolic eltype or contains elements that are
    # symbolic or arrays of symbolics
    return O isa AbstractArray && symbolic_type(O) == NotSymbolic() &&
        (symbolic_type(eltype(O)) != NotSymbolic() && !(eltype(O) <: Union{Symbol, Expr}) ||
        any(_is_tuple_or_array_of_symbolics, O))
end

# workaround for https://github.com/JuliaSparse/SparseArrays.jl/issues/599
function _is_array_of_symbolics(O::SparseMatrixCSC)
    return symbolic_type(eltype(O)) != NotSymbolic() && !(eltype(O) <: Union{Symbol, Expr}) ||
        any(_is_tuple_or_array_of_symbolics, findnz(O)[3])
end

function _is_tuple_of_symbolics(O::Tuple)
    return any(_is_tuple_or_array_of_symbolics, O)
end
_is_tuple_of_symbolics(O) = false

@inline function BSImpl.Const{T}(val; unsafe = false) where {T}
    @nospecialize val
    val = unwrap(val)
    if val isa BasicSymbolic{T}
        return val
    elseif val isa BasicSymbolic{SymReal}
        error("Cannot construct `BasicSymbolic{$T}` from `BasicSymbolic{SymReal}`.")
    elseif val isa BasicSymbolic{SafeReal}
        error("Cannot construct `BasicSymbolic{$T}` from `BasicSymbolic{SymReal}`.")
    elseif val isa BasicSymbolic{TreeReal}
        error("Cannot construct `BasicSymbolic{$T}` from `BasicSymbolic{TreeReal}`.")
    elseif val isa AbstractArray && _is_array_of_symbolics(val)
        args = ArgsT{T}((BSImpl.Const{T}(size(val); unsafe), BSImpl.Const{T}(false; unsafe)))
        sizehint!(args, length(val) + 2)
        type = Union{}
        for v in val
            push!(args, BSImpl.Const{T}(v))
            type = promote_type(type, symtype(v))
        end
        shape = ShapeVecT(axes(val))
        return BSImpl.Term{T}(hvncat, args; type = Array{type, ndims(val)}, shape, unsafe)
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
    shape = parse_shape(shape)
    props = ordered_override_properties(BSImpl.Sym)
    var = BSImpl.Sym{T}(name, metadata, shape, type, props...)
    if !unsafe
        var = hashcons(var)
    end
    return var
end

@inline function BSImpl.Term{T}(f, args; metadata = nothing, type, shape = default_shape(type), unsafe = false) where {T}
    metadata = parse_metadata(metadata)
    shape = parse_shape(shape)
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
    shape = parse_shape(shape)
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
    shape = parse_shape(shape)
    num = Const{T}(num)
    den = Const{T}(den)
    props = ordered_override_properties(BSImpl.Div)
    var = BSImpl.Div{T}(num, den, simplified, metadata, shape, type, props...)
    if !unsafe
        var = hashcons(var)
    end
    return var
end

const DEFAULT_RANGES_SYMREAL = RangesT{SymReal}()
const DEFAULT_RANGES_SAFEREAL = RangesT{SafeReal}()
const DEFAULT_RANGES_TREEREAL = RangesT{TreeReal}()

default_ranges(::Type{SymReal}) = DEFAULT_RANGES_SYMREAL
default_ranges(::Type{SafeReal}) = DEFAULT_RANGES_SAFEREAL
default_ranges(::Type{TreeReal}) = DEFAULT_RANGES_TREEREAL

@inline function BSImpl.ArrayOp{T}(output_idx, expr::BasicSymbolic{T}, reduce, term, ranges = default_ranges(T); metadata = nothing, type, shape = default_shape(type), unsafe = false) where {T}
    metadata = parse_metadata(metadata)
    shape = parse_shape(shape)
    output_idx = parse_output_idxs(T, output_idx)
    term = unwrap_const(unwrap(term))
    ranges = parse_rangedict(T, ranges)
    props = ordered_override_properties(BSImpl.ArrayOp{T})
    var = BSImpl.ArrayOp{T}(output_idx, expr, reduce, term, ranges, metadata, shape, type, props...)
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
struct ArrayOp{T} end

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
            return (k * v)::BasicSymbolic{T}
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
            return (k ^ v)::BasicSymbolic{T}
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

struct IndexedAxis{T}
    sym::BasicSymbolic{T}
    dim::Int
    pad::Union{Int, Nothing}
end

const IdxToAxesT{T} = Dict{BasicSymbolic{T}, Vector{IndexedAxis{T}}}

struct IndexedAxes{T}
    idx_to_axes::IdxToAxesT{T}
    search_buffer::Set{BasicSymbolic{T}}
    buffers::Vector{Vector{IndexedAxis{T}}}
end

function IndexedAxes{T}() where {T}
    IndexedAxes{T}(IdxToAxesT{T}(), Set{BasicSymbolic{T}}(), Vector{IndexedAxis{T}}[])
end

function Base.empty!(ix::IndexedAxes)
    append!(ix.buffers, values(ix.idx_to_axes))
    empty!(ix.search_buffer)
    empty!(ix.idx_to_axes)
    return ix
end

function getbuffer(ix::IndexedAxes{T}) where {T}
    if isempty(ix.buffers)
        return IndexedAxis{T}[]
    else
        return empty!(pop!(ix.buffers))
    end
end

function Base.setindex!(ix::IndexedAxes{T}, val::IndexedAxis{T}, ax::BasicSymbolic{T}) where {T}
    buffer = get!(() -> getbuffer(ix), ix.idx_to_axes, ax)
    push!(buffer, val)
    return ix
end

const INDEXED_AXES_BUFFER_SYMREAL = TaskLocalValue{IndexedAxes{SymReal}}(IndexedAxes{SymReal})
const INDEXED_AXES_BUFFER_SAFEREAL = TaskLocalValue{IndexedAxes{SafeReal}}(IndexedAxes{SafeReal})

for T in [SymReal, SafeReal, TreeReal]
    @eval function _is_index_variable(expr::BasicSymbolic{$T})
        iscall(expr) && operation(expr) === getindex && first(arguments(expr)) === idxs_for_arrayop($T)
    end
end

function get_indexed_axes!(ix::IndexedAxes{T}, expr::BasicSymbolic{T}) where {T}
    iscall(expr) || return ix
    args = arguments(expr)
    if operation(expr) !== getindex
        for arg in args
            get_indexed_axes!(ix, arg)
        end
        return ix
    end

    sym, idxs = Iterators.peel(args)
    for (dim, idx) in enumerate(idxs)
        # special case `i` and `i + offset` for performance
        @match idx begin
            BSImpl.Const(;) => continue
            BSImpl.Sym(;) => begin
                ix[idx] = IndexedAxis(sym, dim, 0)
                continue
            end
            BSImpl.AddMul(; variant, coeff, dict) && if variant == AddMulVariant.ADD && length(dict) == 1 && !iscall(first(keys(dict))) && isone(first(values(dict))) end => begin
                idxsym = first(keys(dict))
                ix[idxsym] = IndexedAxis(sym, dim, Int(coeff))
                continue
            end
            _ => nothing
        end
        vars = ix.search_buffer
        empty!(vars)
        search_variables!(vars, idx; is_atomic = _is_index_variable)
        if length(vars) != 1
            throw(ArgumentError("""
            Expected $dim-th index of $expr to be a function of a single index variable. \
            Found expression $idx involving variables $vars.
            """))
        end
        idxsym = first(vars)
        _pad = idx - idxsym
        # either it's `i + offset` in a non-special-cased form, or it's a more complicated function
        # and we use `nothing` as a sentinel.
        pad = isconst(_pad) ? Int(unwrap_const(_pad)) : nothing
        ix[first(vars)] = IndexedAxis(sym, dim, pad)
    end
    return ix
end

function get_indexed_axes(expr::BasicSymbolic{SymReal})
    buffer = INDEXED_AXES_BUFFER_SYMREAL[]
    empty!(buffer)
    get_indexed_axes!(buffer, expr)
end

function get_indexed_axes(expr::BasicSymbolic{SafeReal})
    buffer = INDEXED_AXES_BUFFER_SAFEREAL[]
    empty!(buffer)
    get_indexed_axes!(buffer, expr)
end

function arrayop_shape(output_idx::AbstractVector, expr::BasicSymbolic{T}, ranges::AbstractDict) where {T}
    ix = get_indexed_axes(expr)
    idx_to_axes = ix.idx_to_axes

    for (idxsym, iaxes) in idx_to_axes
        if haskey(ranges, idxsym)
            is_bound = true
            offset = 1
            reference_axis = ranges[idxsym]
        else
            is_bound = false
            offset = findfirst(iaxes) do iaxis
                !(shape(iaxis.sym) isa Unknown)
            end
            offset === nothing && continue
            iaxis = iaxes[offset]
            reference_axis = (shape(iaxis.sym)::ShapeVecT)[iaxis.dim]
        end

        for i in (offset + 1):length(iaxes)
            iaxis = iaxes[i]
            sh = shape(iaxis.sym)
            sh isa Unknown && continue
            sh = sh::ShapeVecT
            if is_bound
                iaxis.pad === nothing && continue
                if !issubset(reference_axis .+ iaxis.pad, sh[iaxis.dim])
                    throw(ArgumentError("""
                    Expected bound range $reference_axis of $idxsym with offset \
                    $(iaxis.pad) to be within bounds \
                    of dimension $(iaxis.dim) of variable $(iaxis.sym) ($(sh[iaxis.dim])) \
                    where it is used.
                    """))
                end
            else
                if !isequal(length(reference_axis), length(sh[iaxis.dim]))
                    throw(ArgumentError("""
                    Expected all usages of index variable $idxsym be in axes of equal \
                    range. Found usage in dimension $(iaxis.dim) of variable $(iaxis.sym) \
                    which has range $(sh[iaxis.dim]) different from inferred range \
                    $reference_axis.
                    """))
                end
            end
        end
    end

    result = ShapeVecT()
    for idx in output_idx
        if idx isa Int
            push!(result, 1:1)
        elseif idx isa BasicSymbolic{T}
            if haskey(ranges, idx)
                push!(result, 1:length(ranges[idx]))
                continue
            end
            if !haskey(idx_to_axes, idx)
                throw(ArgumentError("Could not infer range of output index $idx."))
            end
            iaxes = idx_to_axes[idx]
            canonical_axis_idx = findfirst(iaxes) do iaxis
                !(shape(iaxis.sym) isa Unknown)
            end
            if canonical_axis_idx === nothing
                return Unknown(length(output_idx))
            end
            canonical_axis = iaxes[canonical_axis_idx]
            push!(result, shape(canonical_axis.sym)[canonical_axis.dim])
        end
    end
    return result
end

function promote_symtype(::Type{ArrayOp{T}}, _outidx, expr, _reduce, _term, _ranges) where {T}
    Array{expr}
end

function ArrayOp{T}(output_idx, expr, reduce, term, ranges; metadata = nothing, unsafe = false) where {T}
    type = Array{symtype(expr), length(output_idx)}
    output_idx = unwrap_args(collect(unwrap(output_idx)))
    expr = unwrap(expr)
    ranges = unwrap_dict(unwrap_const(ranges))
    reduce = unwrap_const(reduce)
    term = unwrap_const(unwrap(term))
    sh = arrayop_shape(collect(unwrap(output_idx)), unwrap(expr), unwrap_const(ranges))
    if term !== nothing && shape(term) != sh
        throw(ArgumentError("""
        Shape of `term` $term provided to `ArrayOp` ($(shape(term))) must be identical to \
        inferred shape $sh.
        """))
    end
    return BSImpl.ArrayOp{T}(output_idx, expr, reduce, term, ranges; type, shape = sh, metadata, unsafe)
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
function term(f, args...; vartype = SymReal, type = promote_symtype(f, symtype.(args)...), shape = promote_shape(f, SymbolicUtils.shape.(args)...))
    @nospecialize f
    Term{vartype}(f, args; type, shape)
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
    elseif f === ArrayOp{T}
        return ArrayOp{T}(args...)
    elseif f === broadcast
        _f, _args = Iterators.peel(args)
        res = broadcast(unwrap_const(_f), _args...)
        if metadata !== nothing && iscall(res)
            @set! res.metadata = metadata
        end
        return res
    elseif f === getindex
        res = getindex(unwrap_const.(args)...)
        if metadata !== nothing && iscall(res)
            @set! res.metadata = metadata
        end
        return res
    elseif _numeric_or_arrnumeric_type(type)
        if f === (+)
            res = add_worker(T, args)
            if metadata !== nothing && (isadd(res) || (isterm(res) && operation(res) == (+)))
                @set! res.metadata = metadata
            end
            return res
        elseif f === (-)
            if length(args) == 1
                res = mul_worker(T, (-1, args[1]))
            else
                res = add_worker(T, (args[1], -args[2]))
            end
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
        sh = promote_shape(f, shape.(args)...)
        Term{T}(f, args; type, shape=sh, metadata=metadata)
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
        BSImpl.Term(; f) && if f isa BasicSymbolic{T} end => is_function_symtype(f)
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
    if x isa Array{<:BasicSymbolic}
        all(_numeric_or_arrnumeric_symtype, x)
    else
        _numeric_or_arrnumeric_type(symtype(x))
    end
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
    if x isa Array{<:BasicSymbolic}
        all(_rational_or_arrrational_symtype, x)
    else
        _rational_or_arrrational_type(symtype(x))
    end
end

@noinline function throw_unequal_shape_error(x, y)
    throw(ArgumentError("Cannot add arguments of different sizes - encountered shapes $x and $y."))
end

promote_shape(::typeof(+), shape::ShapeT) = shape
function promote_shape(::typeof(+), sh1::ShapeT, sh2::ShapeT, shs::ShapeT...)
    @nospecialize sh1 sh2 shs
    nd1 = _ndims_from_shape(sh1)
    nd2 = _ndims_from_shape(sh2)
    nd1 == -1 || nd2 == -1 || nd1 == nd2 || throw_unequal_shape_error(sh1, sh2)
    if sh1 isa Unknown && sh2 isa Unknown
        promote_shape(+, Unknown(max(nd1, nd2)), shs...)
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

function +(x::T, args...) where {T <: NonTreeSym}
    add_worker(vartype(T), (x, args...))
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
    isempty(terms) && return Unknown(-1)
    length(terms) == 1 && return shape(first(terms))
    a, bs = Iterators.peel(terms)
    sh::ShapeT = shape(a)
    for t in bs
        sh = promote_shape(+, sh, shape(t))
    end
    return sh
end

(awb::AddWorkerBuffer{T})(terms) where {T} = awb(Const{T}.(terms))

function (awb::AddWorkerBuffer{T})(terms::Union{Tuple{Vararg{BasicSymbolic{T}}}, AbstractArray{BasicSymbolic{T}}}) where {T}
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
    end
    filter!(!(iszero ∘ last), result)
    isempty(result) && return Const{T}(newcoeff)
    var = Add{T}(newcoeff, result; type, shape)::BasicSymbolic{T}
    @match var begin
        BSImpl.AddMul(; dict) && if dict === result end => (awb.dict = ACDict{T}())
        _ => nothing
    end
    return var
end

const PolyadicNumericOpFirstArgT{T} = Union{Number, AbstractArray{<:Number}, AbstractArray{T}}

function +(a::PolyadicNumericOpFirstArgT{T}, b::T, bs...) where {T <: NonTreeSym}
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
                    return Mul{T}(-coeff, dict; shape, type)::BasicSymbolic{T}
                end
            end
        end
        _ => (-1 * a)::BasicSymbolic{T}
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
        _ => return add_worker(T, (a, -b))::BasicSymbolic{T}
    end
end

-(a::Union{Number, AbstractArray{<:Number}}, b::BasicSymbolic) = a + (-b)
-(a::BasicSymbolic, b::Union{Number, AbstractArray{<:Number}}) = a + (-b)
function -(a::AbstractArray{<:BasicSymbolic}, b::BasicSymbolic)
    Const{vartype(b)}(a) + (-b)
end
function -(a::BasicSymbolic, b::AbstractArray{<:BasicSymbolic})
    a - Const{vartype(a)}(b)
end


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
    first_arr === nothing && return ShapeVecT(), first_arr
    last_arr::Int = findlast(_is_array_shape, shapes)
    first_arr == last_arr && return shapes[first_arr], first_arr

    sh1::ShapeT = shapes[first_arr]
    shend::ShapeT = shapes[last_arr]
    ndims_1 = _ndims_from_shape(sh1)
    ndims_end = _ndims_from_shape(shend)
    ndims_1 == -1 || ndims_1 == 2 || throw_expected_matrix(sh1)
    ndims_end <= 2 || throw_expected_matvec(shend)
    if ndims_end == 1
        # NOTE: This lies because the shape of a matvec mul isn't solely determined by the
        # shapes of inputs. If the first array is an adjoint or transpose, the result
        # is a scalar.
        result = sh1 isa Unknown ? Unknown(1) : ShapeVecT((sh1[1],))
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

    return result, first_arr
end

function promote_shape(::typeof(*), shs::ShapeT...)
    _multiplied_shape(shs)[1]
end

const AdjointOrTranspose = Union{LinearAlgebra.Adjoint, LinearAlgebra.Transpose}

function _check_adjoint_or_transpose(terms, result::ShapeT, first_arr::Union{Int, Nothing})
    @nospecialize first_arr result
    first_arr === nothing && return result
    farr = terms[first_arr]
    if result isa ShapeVecT && length(result) == 1 && length(result[1]) == 1 && (farr isa AdjointOrTranspose || iscall(farr) && (operation(farr) === adjoint || operation(farr) === transpose))
        return ShapeVecT()
    end
    return result
end

function _multiplied_terms_shape(terms::Tuple)
    result, first_arr = _multiplied_shape(ntuple(shape ∘ Base.Fix1(getindex, terms), Val(length(terms))))
    return _check_adjoint_or_transpose(terms, result, first_arr)
end

function _multiplied_terms_shape(terms)
    shapes = SmallV{ShapeT}()
    sizehint!(shapes, length(terms))
    for t in terms
        push!(shapes, shape(t))
    end
    result, first_arr = _multiplied_shape(shapes)
    return _check_adjoint_or_transpose(terms, result, first_arr)
end

function _split_arrterm_scalar_coeff(::Type{T}, ex::BasicSymbolic{T}) where {T}
    sh = shape(ex)
    _is_array_shape(sh) || return ex, Const{T}(1)
    @match ex begin
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
        BSImpl.ArrayOp(; output_idx, expr, reduce, term, ranges, shape, type) => begin
            coeff, rest = @match expr begin
                BSImpl.Term(; f, args, type, shape) && if f === (*) end => begin
                    if query!(isequal(idxs_for_arrayop(T)), args[1])
                        Const{T}(1), expr
                    elseif length(args) == 2
                        args[1], args[2]
                    else
                        newargs = ArgsT{T}()
                        _coeff, rest = Iterators.peel(args)
                        append!(newargs, rest)
                        _coeff, BSImpl.Term{T}(*, newargs; type, shape)
                    end
                end
                _ => (Const{T}(1), expr)
            end
            if term === nothing
                termrest = nothing
            else
                termcoeff, termrest = _split_arrterm_scalar_coeff(T ,term)
                @assert isequal(termcoeff, coeff)
            end
            return coeff, BSImpl.ArrayOp{T}(output_idx, rest, reduce, termrest, ranges; shape, type)
        end
        _ => (Const{T}(1), ex)
    end
end
_split_arrterm_scalar_coeff(::Type{T}, ex) where {T} = Const{T}(1), Const{T}(ex)

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
    if !all(x -> _is_array_of_symbolics(x) || _numeric_or_arrnumeric_symtype(x), terms)
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

    # We're multiplying numbers here. If we don't take the `eltype`
    # and the first element is an array, `promote_symtype` may fail
    # so we take the eltype, since `scalar * scalar` and `scalar * array`
    # both give the correct result regardless of whether the first element
    # is a scalar or array.
    type::TypeT = eltype(symtype(Const{T}(first(terms))))
    arrterms = ArgsT{T}()

    for term in terms
        term = unwrap(term)
        if _is_array_of_symbolics(term)
            term = Const{T}(term)
        end
        sh = shape(term)
        type = promote_symtype(*, type, symtype(term))
        if _is_array_shape(sh)
            coeff, arrterm = _split_arrterm_scalar_coeff(T, term)
            _mul_worker!(T, num_coeff, den_coeff, num_dict, den_dict, coeff)
            if iscall(arrterm) && operation(arrterm) === (*)
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
        if (numexp >= denexp)::Bool
            num_dict[k] = numexp - denexp
            den_dict[k] = 0
        else
            num_dict[k] = 0
            den_dict[k] = denexp - numexp
        end
    end
    filter!(kvp -> !iszero(kvp[2]), num_dict)
    filter!(kvp -> !iszero(kvp[2]), den_dict)

    num_coeff[], den_coeff[] = simplify_coefficients(num_coeff[], den_coeff[])

    num = Mul{T}(num_coeff[], num_dict; type = eltype(type)::TypeT)
    @match num begin
        BSImpl.AddMul(; dict) && if dict === num_dict end => begin
            mwb.num_dict = ACDict{T}()
        end
        _ => nothing
    end
    den = Mul{T}(den_coeff[], den_dict; type = eltype(type)::TypeT)
    @match den begin
        BSImpl.AddMul(; dict) && if dict === den_dict end => begin
            mwb.den_dict = ACDict{T}()
        end
        _ => nothing
    end

    result = Div{T}(num, den, false; type = eltype(type)::TypeT)
    if !isempty(arrterms)
        new_arrterms = ArgsT{T}()
        _nontrivial_coeff = !_isone(result)
        if _nontrivial_coeff
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
            return new_arrterms[1]
        end
        term = Term{T}(*, new_arrterms; type, shape = newshape)
        if newshape === Unknown(-1)
            return term
        end
        @match term begin
            BSImpl.Term(; args) => begin
                if args === new_arrterms
                    new_arrterms = ArgsT{T}()
                else
                    empty!(new_arrterms)
                end
                offset = 0
                if _nontrivial_coeff
                    offset = 1
                    push!(new_arrterms, result)
                end
                idxs = idxs_for_arrayop(T)
                for i in (offset + 1):(length(args) - 1)
                    push!(new_arrterms, args[i][idxs[i - offset], idxs[i - offset + 1]])
                end
                N = length(args)
                if _ndims_from_shape(newshape) == 2
                    push!(new_arrterms, last(args)[idxs[N - offset], idxs[N - offset + 1]])
                    output_idxs = OutIdxT{T}((idxs[1], idxs[N - offset + 1]))
                else
                    push!(new_arrterms, last(args)[idxs[N - offset]])
                    output_idxs = OutIdxT{T}((idxs[1],))
                end
                expr = if length(new_arrterms) == 1
                    new_arrterms[1]
                else
                    Term{T}(*, new_arrterms; type = eltype(type), shape = ShapeVecT())
                end
                return BSImpl.ArrayOp{T}(output_idxs, expr, +, term; type, shape = newshape)
            end
        end
    end
    return result
end

mul_worker(::Type{SymReal}, terms) = SYMREAL_MULBUFFER[](terms)
mul_worker(::Type{SafeReal}, terms) = SAFEREAL_MULBUFFER[](terms)

function *(x::T, args...) where {T <: NonTreeSym}
    mul_worker(vartype(T), (x, args...))
end

function *(a::PolyadicNumericOpFirstArgT{T}, b::T, bs...) where {T <: NonTreeSym}
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
    type = promote_symtype(/, symtype(a), symtype(b))
    newshape = promote_shape(/, shape(a), shape(b))
    Div{T}(a, b, false; type, shape = newshape)
end

function /(a::Union{S,Number,AbstractArray{<:Number}}, b::S) where {S <: NonTreeSym}
    _fslash_worker(vartype(S), a, b)
end
function /(a::AbstractArray{S}, b::S) where {S <: NonTreeSym}
    _fslash_worker(vartype(S), Const{vartype(S)}(a), b)
end

function /(a::S, b::Union{Number,AbstractArray{<:Number}}) where {S <: NonTreeSym}
    _fslash_worker(vartype(S), a, b)
end
function /(a::S, b::AbstractArray{S}) where {S <: NonTreeSym}
    _fslash_worker(vartype(S), a, Const{vartype(S)}(b))
end

function //(a::Union{S,Number,AbstractArray{<:Number}}, b::S) where {S <: NonTreeSym}
    if !_rational_or_arrrational_symtype(a) || !_rational_or_arrrational_symtype(b)
        throw(MethodError(//, (a, b)))
    end
    _fslash_worker(vartype(S), a, b)
end
function //(a::AbstractArray{S}, b::S) where {S <: NonTreeSym}
    a = Const{vartype(S)}(a)
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
function //(a::S, b::AbstractArray{S}) where {S <: NonTreeSym}
    b = Const{vartype(S)}(b)
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
        sha.ndims == -1 && return Unknown(-1)
        shb.ndims == -1 && return Unknown(-1)
        sha.ndims == 1 && shb.ndims == 1 && return ShapeVecT()
        return shb
    elseif sha isa Unknown && shb isa ShapeVecT
        sha.ndims <= 2 || throw_bad_dims(sha, shb)
        length(shb) <= 2 || throw_bad_dims(sha, shb)
        length(shb) == 0 && throw_scalar_rhs(sha, shb)
        sha.ndims == -1 && return Unknown(-1)
        sha.ndims == 1 && ndims_b == 1 && return ShapeVecT()
        sha.ndims == 1 && ndims_b == 2 && return ShapeVecT((1:1, shb[2]))
        sha.ndims == 2 && return Unknown(ndims_b)
        _unreachable()
    elseif sha isa ShapeVecT && shb isa Unknown
        shb.ndims == -1 && return Unknown(-1)
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
function \(a::AbstractArray{S}, b::S) where {S <: NonTreeSym}
    a = Const{vartype(S)}(a)
    _bslash_worker(vartype(S), a, b)
end
function \(a::T, b::AbstractArray{T}) where {T <: NonTreeSym}
    b = Const{vartype(T)}(b)
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
        sh1.ndims == 2 || sh1.ndims == -1 || throw_nonmatbase(sh1)
        return Unknown(2) # either the result is a matrix or the operation will error
    elseif sh1 isa ShapeVecT && sh2 isa Unknown
        isempty(sh1) || throw_matmatpow(sh1, sh2)
        sh2.ndims == 2 || sh2.ndims == -1 || throw_nonmatexp(sh2)
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
                return (coeff ^ b * rest ^ b)
            end
            _ => return Term{T}(^, ArgsT{T}((a, Const{T}(b))); type, shape = newshape)
        end
    elseif _is_array_shape(shb)
        return Term{T}(^, ArgsT{T}((a, Const{T}(b))); type, shape = newshape)::BasicSymbolic{T}
    end
    if b isa Number
        iszero(b) && return Const{T}(1)
        isone(b) && return Const{T}(a)
    end
    if b isa Real && b < 0
        return Div{T}(1, a ^ (-b), false; type)::BasicSymbolic{T}
    end
    if b isa Number
        @match a begin
            BSImpl.Term(; f, args) && if f === (^) && isconst(args[2]) && symtype(args[2]) <: Number end => begin
                base, exp = args
                base, exp = arguments(a)
                exp = unwrap_const(exp)
                return Const{T}(base ^ (exp * b))
            end
            BSImpl.Term(; f, args) && if f === sqrt && (safe_isinteger(b) && Int(b) % 2 == 0 || b isa Rational && numerator(b)%2 == 0) end => begin
                exp = safe_isinteger(b) ? (Int(b) // 2) : (b // 2)
                return Const{T}(args[1] ^ exp)
            end
            BSImpl.Term(; f, args) && if f === cbrt && (safe_isinteger(b) && Int(b) % 3 == 0 || b isa Rational && numerator(b)%3 == 0) end => begin
                exp = safe_isinteger(b) ? (Int(b) // 3) : (b // 3)
                return Const{T}(args[1] ^ exp)
            end
            _ => nothing
        end
    end
    @match a begin
        BSImpl.Div(; num, den) => return BSImpl.Div{T}(num ^ b, den ^ b, false; type)
        _ => nothing
    end
    if b isa Number
        @match a begin
            BSImpl.AddMul(; coeff, dict, variant, shape, type) && if variant == AddMulVariant.MUL end => begin
                if coeff isa Real && coeff < 0 && !safe_isinteger(b)
                    coeff = (-coeff) ^ b
                    newmul = BSImpl.AddMul{T}(-1, dict, variant; shape, type)
                    # newpow = Term{T}(^, ArgsT{T}((newmul, b)); shape, type)
                    if _isone(coeff)
                        return Term{T}(^, ArgsT{T}((newmul, b)); shape, type)
                    else
                        return BSImpl.AddMul{T}(coeff, ACDict{T}(newmul => b), AddMulVariant.MUL; shape, type)
                    end
                    # return mul_worker(T, (coeff, newpow))
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
    isconst(b) && return Const{T}(a ^ unwrap_const(b))
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
function ^(a::Matrix{BasicSymbolic{T}}, b::BasicSymbolic{T}) where {T <: Union{SafeReal, SymReal}}
    Const{T}(a) ^ b
end
function ^(a::BasicSymbolic{T}, b::Matrix{BasicSymbolic{T}}) where {T <: Union{SafeReal, SymReal}}
    a ^ Const{T}(b)
end

abstract type Operator end
promote_shape(::Operator, @nospecialize(shx::ShapeT)) = shx
promote_symtype(::Operator, ::Type{T}) where {T} = T

@inline _indexed_ndims() = 0
@inline _indexed_ndims(::Type{T}, rest...) where {T <: Integer} = _indexed_ndims(rest...)
@inline _indexed_ndims(::Type{<:AbstractVector{<:Integer}}, rest...) = 1 + _indexed_ndims(rest...)
@inline _indexed_ndims(::Type{Colon}, rest...) = 1 + _indexed_ndims(rest...)
@inline _indexed_ndims(::Type{T}, rest...) where {T} = throw(ArgumentError("Invalid index type $T."))

function promote_symtype(::typeof(getindex), ::Type{T}, Ts::Vararg{Any, N}) where {N, eT, T <: AbstractArray{eT, N}}
    nD = _indexed_ndims(Ts...)
    nD == 0 ? eT : Array{eT, nD}
end

function promote_symtype(::typeof(getindex), ::Type{T}, Ts...) where {eT, T <: AbstractArray{eT}}
    nD = _indexed_ndims(Ts...)
    nD == 0 ? eT : Array{eT, nD}
end

function promote_symtype(::typeof(getindex), ::Type{T}) where {T <: Number}
    T
end

promote_symtype(::typeof(getindex), ::Type{Symbol}, Ts...) = Any

function promote_symtype(::typeof(getindex), ::Type{T}, Ts...) where {N, eT, T <: AbstractArray{eT, N}}
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
    _is_array_shape(sharr) || isempty(shidxs) || throw_not_array(sharr)
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

Base.@propagate_inbounds function Base.getindex(arr::BasicSymbolic{T}, idxs::Union{BasicSymbolic{T}, Int, AbstractRange{Int}, Colon}...) where {T}
    if T === SymReal
        return _getindex_1(arr, idxs...)
    elseif T === SafeReal
        return _getindeX_2(arr, idxs...)
    end
    _unreachable()
end

@cache function _getindex_1(arr::BasicSymbolic{SymReal}, idxs::Union{BasicSymbolic{SymReal}, Int, AbstractRange{Int}, Colon}...)::BasicSymbolic{SymReal}
    _getindex(arr, idxs...)
end
@cache function _getindex_2(arr::BasicSymbolic{SafeReal}, idxs::Union{BasicSymbolic{SafeReal}, Int, AbstractRange{Int}, Colon}...)::BasicSymbolic{SafeReal}
    _getindex(arr, idxs...)
end

Base.@propagate_inbounds function _getindex(arr::BasicSymbolic{T}, idxs::Union{BasicSymbolic{T}, Int, AbstractRange{Int}, Colon}...) where {T}
    @match arr begin
        BSImpl.Term(; f) && if f === hvncat && all(x -> !(x isa BasicSymbolic{T}) || isconst(x), idxs) end => begin
            return Const{T}(reshape(@view(arguments(arr)[3:end]), Tuple(size(arr)))[unwrap_const.(idxs)...])
        end
        BSImpl.Term(; f, args) && if f isa TypeT && f <: CartesianIndex end => return args[idxs...]
        BSImpl.Term(; f, args) && if f isa Operator && length(args) == 1 end => begin
            inner = args[1][idxs...]
            return BSImpl.Term{T}(f, ArgsT{T}((inner,)); type = symtype(inner), shape = shape(inner))
        end
        BSImpl.Term(; f, args) && if f === getindex && all(isconst, Iterators.drop(args, 1)) && !any(x -> x isa BasicSymbolic{T}, idxs) end => begin
            newargs = ArgsT{T}()
            push!(newargs, args[1])
            sh = shape(arr)
            type = promote_symtype(getindex, symtype(arr), symtype.(idxs)...)
            newshape = promote_shape(getindex, sh, shape.(idxs)...)
            for (oldidx, idx) in zip(Iterators.drop(args, 1), idxs)
                if idx isa Colon
                    push!(newargs, oldidx)
                else
                    push!(newargs, Const{T}(unwrap_const(oldidx)[idx]))
                end
            end
            return BSImpl.Term{T}(f, newargs; type, shape = newshape)
        end
        _ => nothing
    end

    sh = shape(arr)
    type = promote_symtype(getindex, symtype(arr), symtype.(idxs)...)
    newshape = promote_shape(getindex, sh, shape.(idxs)...)
    @boundscheck if sh isa ShapeVecT
        for (ax, idx) in zip(sh, idxs)
            idx isa BasicSymbolic{T} && continue
            idx isa Colon && continue
            checkindex(Bool, ax, idx) || throw(BoundsError(arr, idxs))
        end
    end
    @match arr begin
        BSImpl.ArrayOp(; output_idx, expr, ranges, reduce, term) => begin
            subrules = Dict{BasicSymbolic{T}, Union{BasicSymbolic{T}, Int}}()
            empty!(subrules)
            new_output_idx = OutIdxT{T}()
            new_ranges = RangesT{T}()
            idxsym_idx = 1
            idxsym = idxs_for_arrayop(T)
            for (i, (newidx, outidx)) in enumerate(zip(idxs, output_idx))
                if outidx isa Int
                    newidx isa Colon && push!(new_output_idx, outidx)
                elseif outidx isa BasicSymbolic{T}
                    if newidx isa Colon
                        new_out_idx = idxsym[idxsym_idx]
                        if !isequal(outidx, new_out_idx)
                            subrules[outidx] = new_out_idx
                        end
                        push!(new_output_idx, new_out_idx)
                        idxsym_idx += 1
                    elseif newidx isa AbstractRange{Int}
                        new_out_idx = idxsym[idxsym_idx]
                        if !isequal(outidx, new_out_idx)
                            subrules[outidx] = new_out_idx
                        end
                        push!(new_output_idx, new_out_idx)
                        idxsym_idx += 1
                        if haskey(ranges, outidx)
                            new_ranges[new_out_idx] = ranges[outidx][newidx]
                        else
                            new_ranges[new_out_idx] = newidx
                        end
                    else
                        if haskey(ranges, outidx)
                            subrules[outidx] = ranges[outidx][unwrap_const(newidx)::Union{BasicSymbolic{T}, Int}]
                        else
                            subrules[outidx] = unwrap_const(newidx)::Union{BasicSymbolic{T}, Int}
                        end
                    end
                end
            end
            if isempty(new_output_idx)
                new_expr = reduce_eliminated_idxs(expr, output_idx, ranges, reduce)
                result = substitute(new_expr, subrules; fold = false, filterer = !isarrayop)
                return result
            else
                new_expr = substitute(expr, subrules; fold = false, filterer = !isarrayop)
                if term !== nothing
                    term = getindex(term, idxs...)
                end
                return BSImpl.ArrayOp{T}(new_output_idx, new_expr, reduce, term, new_ranges; type, shape = newshape)
            end
        end
        _ => begin
            if _is_array_shape(newshape)
                new_output_idx = OutIdxT{T}()
                expr_args = ArgsT{T}((arr,))
                term_args = ArgsT{T}((arr,))
                ranges = RangesT{T}()
                idxsym_idx = 1
                idxsym = idxs_for_arrayop(T)
                for idx in idxs
                    push!(term_args, Const{T}(idx))
                    if idx isa Int
                        push!(expr_args, Const{T}(idx))
                    elseif idx isa Colon
                        new_idx = idxsym[idxsym_idx]
                        push!(new_output_idx, new_idx)
                        push!(expr_args, new_idx)
                        idxsym_idx += 1
                    elseif idx isa AbstractRange{Int}
                        new_idx = idxsym[idxsym_idx]
                        push!(new_output_idx, new_idx)
                        push!(expr_args, new_idx)
                        ranges[new_idx] = idx
                        idxsym_idx += 1
                    elseif idx isa BasicSymbolic{T}
                        push!(expr_args, idx)
                    end
                end
                new_expr = BSImpl.Term{T}(getindex, expr_args; type = eltype(type), shape = ShapeVecT())
                new_term = BSImpl.Term{T}(getindex, term_args; type, shape = newshape)
                return BSImpl.ArrayOp{T}(new_output_idx, new_expr, +, new_term, ranges; type, shape = newshape)
            else
                return BSImpl.Term{T}(getindex, ArgsT{T}((arr, Const{T}.(idxs)...)); type, shape = newshape)
            end
        end
    end
end
Base.getindex(x::BasicSymbolic{T}, i::CartesianIndex) where {T} = x[Tuple(i)...]
function Base.getindex(x::AbstractArray, idx::BasicSymbolic{T}, idxs...) where {T}
    getindex(Const{T}(x), idx, idxs...)
end
function Base.getindex(x::AbstractArray, i1, idx::BasicSymbolic{T}, idxs...) where {T}
    getindex(Const{T}(x), i1, idx, idxs...)
end
function Base.getindex(x::AbstractArray, i1, i2, idx::BasicSymbolic{T}, idxs...) where {T}
    getindex(Const{T}(x), i1, i2, idx, idxs...)
end
