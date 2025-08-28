export SymReal, SafeReal, TreeReal, vartype

abstract type SymVariant end
abstract type SymReal <: SymVariant end
abstract type SafeReal <: SymVariant end
abstract type TreeReal <: SymVariant end

###
### Uni-type design
###

struct Unknown end

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
    struct Polyform
        # polynomial in terms of full hashed variables
        const poly::PolynomialT
        # corresponding to poly.x.vars, the partially hashed variables
        const partial_polyvars::Vector{PolyVarT}
        # corresponding to poly.x.vars, the BasicSymbolic variables
        const vars::SmallV{BasicSymbolicImpl.Type{T}}
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
        hash2::UInt
        id::IdentT
    end
end

const BSImpl = BasicSymbolicImpl
const BasicSymbolic = BSImpl.Type
const ArgsT{T} = SmallV{BasicSymbolic{T}}
const ROArgsT{T} = ReadOnlyVector{BasicSymbolic{T}, ArgsT{T}}

const POLYVAR_LOCK = ReadWriteLock()
# NOTE: All of these are accessed via POLYVAR_LOCK
const BS_TO_PVAR = WeakKeyDict{BasicSymbolic, PolyVarT}()
const BS_TO_PARTIAL_PVAR = WeakKeyDict{BasicSymbolic, PolyVarT}()
const PVAR_TO_BS = Dict{Symbol, WeakRef}()

# TODO: manage scopes better here
function basicsymbolic_to_polyvar(x::BasicSymbolic)::PolyVarT
    pvar = partial_pvar = name = partial_name = nothing
    @manually_scope COMPARE_FULL => true begin
        @readlock POLYVAR_LOCK begin
            pvar = get(BS_TO_PVAR, x, nothing)

            if pvar !== nothing
                return pvar
            end

            inner_name = _name_as_operator(x)
            name = Symbol(inner_name, :_, hash(x))
            while (cur = get(PVAR_TO_BS, name, nothing); cur !== nothing && cur.value !== nothing)
                # `cache` didn't have a mapping for `x`, so `rev_cache` cannot have
                # a valid mapping for the polyvar (name)
                name = Symbol(name, :_)
            end

            @manually_scope COMPARE_FULL => false begin
                # do the same thing, but for the partial hash
                partial_name = Symbol(inner_name, :_, hash(x))
            end true
        end
        @lock POLYVAR_LOCK begin
            # NOTE: This _MUST NOT_ give away the lock between creating the polyvar
            # and partial polyvar. Currently, this invariant enforces that the two are
            # created sequentially. Since variables are ordered by creation order,
            # this means that the relative ordering between PVARs of two symbolics
            # is the same as the relative ordering between their PARTIAL_PVARs. This
            # allows us to swap out the vector of variables in the polynomial while
            # maintaining the ordering invariant.
            pvar = MP.similar_variable(ExamplePolyVar, name)
            partial_pvar = MP.similar_variable(ExamplePolyVar, partial_name)
            BS_TO_PARTIAL_PVAR[x] = partial_pvar
            BS_TO_PVAR[x] = pvar
            PVAR_TO_BS[name] = WeakRef(x)
        end
    end
    return pvar
end

function basicsymbolic_to_partial_polyvar(x::BasicSymbolic)::PolyVarT
    basicsymbolic_to_polyvar(x)
    @manually_scope COMPARE_FULL => true begin
        return @readlock POLYVAR_LOCK BS_TO_PARTIAL_PVAR[x]
    end
end

function polyvar_to_basicsymbolic(x::PolyVarT)
    name = Symbol(MP.name(x))
    bs = @readlock POLYVAR_LOCK get(PVAR_TO_BS, name, nothing)
    if bs === nothing
        error("Invalid polyvar $x")
    end
    bs = bs.value
    if bs === nothing
        error("Invalid polyvar $x")
    end
    return bs::BasicSymbolic
end

function subs_poly(poly::Union{PolynomialT, MP.Term}, vars)
    add_buffer = ArgsT()
    mul_buffer = ArgsT()
    for term in MP.terms(poly)
        empty!(mul_buffer)
        coeff = MP.coefficient(term)
        push!(mul_buffer, closest_const(coeff))
        mono = MP.monomial(term)
        for (i, exp) in enumerate(MP.exponents(mono))
            iszero(exp) && continue
            push!(mul_buffer, (vars[i] ^ exp))
        end
        push!(add_buffer, mul_worker(mul_buffer))
    end
    return add_worker(add_buffer)
end

function symtype(x::BasicSymbolic)
    # use `@match` instead of `x.type` since it is faster
    @match x begin
        BSImpl.Const(; val) => typeof(val)
        BSImpl.Sym(; type) => type
        BSImpl.Term(; type) => type
        BSImpl.Polyform(; type) => type
        BSImpl.Div(; type) => type
    end
end
symtype(x) = typeof(x)

vartype(x::BasicSymbolic{T}) where {T} = T
vartype(::Type{BasicSymbolic{T}}) where {T} = T

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
        ::Type{<:BSImpl.Sym} => (; id = (nothing, nothing), hash2 = 0)
        ::Type{<:BSImpl.Polyform} => (; id = (nothing, nothing), hash = 0, hash2 = 0)
        ::Type{<:BSImpl.Term} => (; id = (nothing, nothing), hash = 0, hash2 = 0)
        ::Type{<:BSImpl.Div} => (; id = (nothing, nothing), hash2 = 0)
        _ => throw(UnimplementedForVariantError(override_properties, obj))
    end
end

function ordered_override_properties(obj::Type{<:BSImpl.Variant})
    @match obj begin
        ::Type{<:BSImpl.Const} => ((nothing, nothing),)
        ::Type{<:BSImpl.Sym} => (0, (nothing, nothing))
        ::Type{<:BSImpl.Term} => (0, 0, (nothing, nothing))
        ::Type{<:BSImpl.Polyform} => (ArgsT(), 0, 0, (nothing, nothing))
        ::Type{<:BSImpl.Div} => (0, (nothing, nothing))
        _ => throw(UnimplementedForVariantError(override_properties, obj))
    end
end

function ConstructionBase.getproperties(obj::BSImpl.Type)
    @match obj begin
        BSImpl.Const(; val, id) => (; val, id)
        BSImpl.Sym(; name, metadata, hash2, shape, id) => (; name, metadata, hash2, shape, id)
        BSImpl.Term(; f, args, metadata, hash, hash2, shape, id) => (; f, args, metadata, hash, hash2, shape, id)
        BSImpl.Polyform(; poly, partial_polyvars, vars, metadata, shape, args, hash, hash2, id) => (; poly, partial_polyvars, vars, metadata, shape, args, hash, hash2, id)
        BSImpl.Div(; num, den, simplified, metadata, hash2, shape, id) => (; num, den, simplified, metadata, hash2, shape, id)
    end
end

function ConstructionBase.setproperties(obj::BSImpl.Type, patch::NamedTuple)
    props = getproperties(obj)
    overrides = override_properties(obj)
    # We only want to invalidate `args` if we're updating `coeff` or `dict`.
    if ispolyform(obj)
        extras = (; args = ArgsT())
    else
        extras = (;)
    end
    hashcons(MData.variant_type(obj)(; props..., patch..., overrides..., extras...)::typeof(obj))
end

###
### Term interface
###

@enumx PolyformVariant::UInt8 begin
    ADD
    MUL
    POW
end

function polyform_variant(x::BasicSymbolic)
    ispolyform(x) || throw(ArgumentError("Cannot call `polyform_variant` on non-polyform"))
    poly = MData.variant_getfield(x, BSImpl.Polyform, :poly)
    polyform_variant(poly)
end
function polyform_variant(poly::PolynomialT)
    if MP.nterms(poly) > 1
        return PolyformVariant.ADD
    end
    term = only(MP.terms(poly))
    if !isone(MP.coefficient(term))
        return PolyformVariant.MUL
    end
    mono = MP.monomial(term)
    nnz = count(!iszero, MP.exponents(mono))
    if iszero(nnz)
        error("Polyform cannot be an empty polynomial")
    elseif isone(nnz)
        return PolyformVariant.POW
    else
        return PolyformVariant.MUL
    end
end

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
        BSImpl.Polyform(; poly) => @match polyform_variant(poly) begin
            PolyformVariant.ADD => (+)
            PolyformVariant.MUL => (*)
            PolyformVariant.POW => (^)
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
    @match x begin
        BSImpl.Polyform(; poly) => begin
            variant = polyform_variant(poly)
            args = copy(parent(arguments(x)))
            @match variant begin
                PolyformVariant.ADD => sort!(args, by = get_degrees, lt = monomial_lt)
                PolyformVariant.MUL => sort!(args, by = get_degrees)
                _ => nothing
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
function TermInterface.arguments(x::BSImpl.Type{T})::ROArgsT where {T}
    @match x begin
        BSImpl.Const(_) => throw(ArgumentError("`Const` does not have arguments."))
        BSImpl.Sym(_) => throw(ArgumentError("`Sym` does not have arguments."))
        BSImpl.Term(; args) => ROArgsT(args)
        BSImpl.Polyform(; poly, partial_polyvars, vars, args, shape) => begin
            isempty(args) || return ROArgsT(args)
            @match polyform_variant(poly) begin
                PolyformVariant.ADD => begin
                    for term in MP.terms(poly)
                        coeff = MP.coefficient(term)
                        mono = MP.monomial(term)
                        exps = MP.exponents(mono)
                        if MP.isconstant(term)
                            push!(args, closest_const(coeff))
                        elseif isone(coeff) && isone(count(!iszero, exps))
                            idx = findfirst(!iszero, exps)
                            push!(args, vars[idx] ^ exps[idx])
                        else
                            push!(args, Polyform{T}(MP.polynomial(term, T), partial_polyvars, vars; shape))
                        end
                    end
                end
                PolyformVariant.MUL => begin
                    term = only(MP.terms(poly))
                    coeff = MP.coefficient(term)
                    mono = MP.monomial(term)
                    if !isone(coeff)
                        push!(args, closest_const(coeff))
                    end
                    _new_coeffs = ones(T, 1)
                    for (i, (var, pow)) in enumerate(zip(vars, MP.exponents(mono)))
                        iszero(pow) && continue
                        if isone(pow)
                            push!(args, var)
                        else
                            exps = zeros(Int, length(vars))
                            exps[i] = pow
                            mvec = DP.MonomialVector(MP.variables(poly), [exps])
                            newpoly = PolynomialT{T}(_new_coeffs, mvec)
                            push!(args, Polyform{T}(newpoly, partial_polyvars, vars))
                        end
                    end
                end
                PolyformVariant.POW => begin
                    term = only(MP.terms(poly))
                    mono = MP.monomial(term)
                    exps = MP.exponents(mono)
                    idx = findfirst(!iszero, exps)
                    pow = exps[idx]
                    @assert !iszero(pow)
                    # @assert !isone(pow)
                    push!(args, vars[idx])
                    push!(args, closest_const(pow))
                end
            end
            return ROArgsT(args)
        end
        BSImpl.Div(num, den) => ROArgsT(ArgsT((num, den)))
        _ => throw(UnimplementedForVariantError(arguments, MData.variant_type(x)))
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
ispolyform(x::BSImpl.Type) = MData.isa_variant(x, BSImpl.Polyform)
isadd(x::BSImpl.Type) = ispolyform(x) && polyform_variant(x) == PolyformVariant.ADD
ismul(x::BSImpl.Type) = ispolyform(x) && polyform_variant(x) == PolyformVariant.MUL
isdiv(x::BSImpl.Type) = MData.isa_variant(x, BSImpl.Div)
ispow(x::BSImpl.Type) = ispolyform(x) && polyform_variant(x) == PolyformVariant.POW

for fname in [:isconst, :issym, :isterm, :ispolyform, :isadd, :ismul, :isdiv, :ispow]
    @eval $fname(x) = false
end

###
### Base interface
###

Base.isequal(::BasicSymbolic, x) = false
Base.isequal(x, ::BasicSymbolic) = false
Base.isequal(::BasicSymbolic, ::Missing) = false
Base.isequal(::Missing, ::BasicSymbolic) = false

const SCALAR_SYMTYPE_VARIANTS = [Number, Real, SafeReal, LiteralReal, Int, Float64, Bool]
const ARR_VARIANTS = [Vector, Matrix]
const SYMTYPE_VARIANTS = [SCALAR_SYMTYPE_VARIANTS; [A{T} for A in ARR_VARIANTS for T in SCALAR_SYMTYPE_VARIANTS]]

@eval Base.@nospecializeinfer function isequal_maybe_scal(a, b, full::Bool)
    @nospecialize a b
    $(begin
        conds = Expr[]
        bodys = Expr[]
        for T in SYMTYPE_VARIANTS
            push!(conds, :(a isa BasicSymbolic{$T} && b isa BasicSymbolic{$T}))
            push!(bodys, :(isequal_bsimpl(a, b, full)))
        end
        for T1 in SCALAR_SYMTYPE_VARIANTS, T2 in SCALAR_SYMTYPE_VARIANTS
            isconcretetype(T1) && isconcretetype(T2) || continue
            push!(conds, :(a isa $T1 && b isa $T2))
            push!(bodys, :(isequal(a, b)))
        end
        for A in ARR_VARIANTS, T in SCALAR_SYMTYPE_VARIANTS
            push!(conds, :(a isa $A{$T} && b isa $A{$T}))
            push!(bodys, :(isequal(a, b)))
        end
        expr = :()
        if !isempty(conds)
            root_cond, rest_conds = Iterators.peel(conds)
            root_body, rest_bodys = Iterators.peel(bodys)
            expr = Expr(:if, root_cond, root_body)
            cur_expr = expr
            for (cond, body) in zip(rest_conds, rest_bodys)
                global cur_expr
                new_chain = Expr(:elseif, cond, body)
                push!(cur_expr.args, new_chain)
                cur_expr = new_chain
            end
            push!(cur_expr.args, :(isequal(a, b)::Bool))
        end
        expr
    end)
end

const COMPARE_FULL = TaskLocalValue{Bool}(Returns(false))

function swap_polynomial_vars(poly::PolynomialT, new_vars::Vector{PolyVarT})
    typeof(poly)(MP.coefficients(poly), DP.MonomialVector(new_vars, MP.monomials(poly).Z))
end

function swap_polynomial_vars(_::PolyVarT, new_vars::Vector{PolyVarT})
    MP.polynomial(only(new_vars))
end

function isequal_bsimpl(a::BSImpl.Type, b::BSImpl.Type, full)
    a === b && return true
    taskida, ida = a.id
    taskidb, idb = b.id
    ida === idb && ida !== nothing && return true
    typeof(a) === typeof(b) || return false

    Ta = MData.variant_type(a)
    Tb = MData.variant_type(b)
    Ta === Tb || return false

    if full && ida !== idb && ida !== nothing && idb !== nothing && taskida == taskidb
        return false
    end

    partial = @match (a, b) begin
        (BSImpl.Const(; val = v1), BSImpl.Const(; val = v2)) => begin
            isequal_maybe_scal(v1, v2, full) && (!full || typeof(v1) == typeof(v2))
        end
        (BSImpl.Sym(; name = n1, shape = s1), BSImpl.Sym(; name = n2, shape = s2)) => begin
            n1 === n2 && s1 == s2
        end
        (BSImpl.Term(; f = f1, args = args1, shape = s1), BSImpl.Term(; f = f2, args = args2, shape = s2)) => begin
            isequal(f1, f2)::Bool && isequal(args1, args2) && s1 == s2
        end
        (BSImpl.Polyform(; poly = p1, partial_polyvars = part1, shape = s1), BSImpl.Polyform(; poly = p2, partial_polyvars = part2, shape = s2)) => begin
            # Polyform is special. If we're doing a full comparison, checking equality of
            # the contained `poly` works (even if they represent the same polynomials but
            # `MP.variables` is different). Since the MP variables in the polynomial are
            # based on the full comparison identity, their equality represents true equality.
            # For partial equality checking, we simply replace `poly.x.vars` with `partial_polyvars`
            # and compare those polynomials.
            s1 == s2 && if full
                isequal(p1, p2)
            else
                poly1 = swap_polynomial_vars(p1, part1)
                poly2 = swap_polynomial_vars(p2, part2)
                isequal(poly1, poly2)
            end
        end
        (BSImpl.Div(; num = n1, den = d1), BSImpl.Div(; num = n2, den = d2)) => begin
            isequal_maybe_scal(n1, n2, full) && isequal_maybe_scal(d1, d2, full)
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

const CONST_SALT = 0x194813feb8a8c83d % UInt
const SYM_SALT = 0x4de7d7c66d41da43 % UInt
const ADD_SALT = 0xaddaddaddaddadda % UInt
const MUL_SALT = 0xaaaaaaaaaaaaaaaa % UInt
const DIV_SALT = 0x334b218e73bbba53 % UInt
const POW_SALT = 0x2b55b97a6efb080c % UInt
const PLY_SALT = 0x36ee940e7fa431a3 % UInt

@eval Base.@nospecializeinfer function hash_anyscalar(x::Any, h::UInt, full::Bool)
    @nospecialize x
    $(begin
        conds = Expr[]
        bodys = Expr[]
        for T in SYMTYPE_VARIANTS
            push!(conds, :(x isa BasicSymbolic{$T}))
            push!(bodys, :(hash_bsimpl(x, h, full)))
        end
        for T in SCALAR_SYMTYPE_VARIANTS
            isconcretetype(T) || continue
            push!(conds, :(x isa $T))
            push!(bodys, :(hash(x, h)))
        end
        for A in ARR_VARIANTS, T in SCALAR_SYMTYPE_VARIANTS
            push!(conds, :(x isa $A{$T}))
            push!(bodys, :(hash(x, h)))
        end

        expr = :()
        if !isempty(conds)
            root_cond, rest_conds = Iterators.peel(conds)
            root_body, rest_bodys = Iterators.peel(bodys)
            expr = Expr(:if, root_cond, root_body)
            cur_expr = expr
            for (cond, body) in zip(rest_conds, rest_bodys)
                global cur_expr
                new_chain = Expr(:elseif, cond, body)
                push!(cur_expr.args, new_chain)
                cur_expr = new_chain
            end
            push!(cur_expr.args, :(hash(x, h)::UInt))
        end

        expr
    end)
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
    if !iszero(h)
        return hash(hash_bsimpl(s, zero(h), full), h)::UInt
    end
    @match s begin
        BSImpl.Const(; val) => begin
            h = hash_anyscalar(val, h, full)
            if full
                h = Base.hash(typeof(val), h)::UInt
            end
            return h
        end
        _ => nothing
    end
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
            if iszero(hash)
                hash = s.hash = Base.hash(f, hashargs(args, Base.hash(shape, h), full))::UInt
            else
                hash
            end
        end
        BSImpl.Polyform(; poly, partial_polyvars, shape, hash) => begin
            if full
                Base.hash(poly, Base.hash(shape, h))
            else
                if iszero(hash)
                    hash = s.hash = Base.hash(swap_polynomial_vars(poly, partial_polyvars), Base.hash(shape, h))
                else
                    hash
                end
            end
        end
        BSImpl.Div(; num, den) => begin
            hash_anyscalar(num, hash_anyscalar(den, h, full), full) ⊻ DIV_SALT
        end
    end

    if full && !isconst(s)
        partial = s.hash2 = Base.hash(metadata(s), partial)::UInt
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

Base.nameof(s::Union{BasicSymbolic, BSImpl.Type}) = issym(s) ? s.name : error("Non-Sym BasicSymbolic doesn't have a name")

###
### Constructors
###

const ENABLE_HASHCONSING = Ref(true)
# const WKD = TaskLocalValue{WeakKeyDict{HashconsingWrapper, Nothing}}(WeakKeyDict{HashconsingWrapper, Nothing})
const WKD = TaskLocalValue{WeakKeyDict{BSImpl.Type, Nothing}}(WeakKeyDict{BSImpl.Type, Nothing})
const WVD = TaskLocalValue{WeakValueDict{UInt, BSImpl.Type}}(WeakValueDict{UInt, BSImpl.Type})
const WCS = TaskLocalValue{WeakCacheSet{BSImpl.Type}}(WeakCacheSet{BSImpl.Type})
const TASK_ID = TaskLocalValue{UInt}(() -> rand(UInt))

function generate_id()
    return (TASK_ID[], IDType())
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

function hashcons(s::BSImpl.Type)
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
        if k.id === (nothing, nothing)
            k.id = generate_id()
        end
        return k::typeof(s)
    end true
end

const SMALLV_DEFAULT = hashcons(BSImpl.Const{Int}(0, (nothing, nothing)))

defaultval(::Type{<:BasicSymbolic}) = SMALLV_DEFAULT

function get_mul_coefficient(x)
    iscall(x) && operation(x) === (*) || throw(ArgumentError("$x is not a multiplication"))
    @match x begin
        BSImpl.Term(; args) => begin
            if ispolyform(args[1]) && polyform_variant(args[1]) == PolyformVariant.MUL
                return MP.coefficient(MP.terms(poly)[1])
            else
                return 1
            end
        end
        BSImpl.Polyform(; poly) => begin
            return MP.coefficient(MP.terms(poly)[1])
        end
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

default_shape(::Type{<:AbstractArray}) = Unknown()
default_shape(_) = ShapeVecT()

"""
    $(METHODLIST)

If `x` is a rational with denominator 1, turn it into an integer.
"""
function maybe_integer(x)
    x = unwrap(x)
    return (x isa Rational && isone(x.den)) ? x.num : x
end

@eval Base.@nospecializeinfer function closest_const(arg)
    @nospecialize arg
    $(begin
        conds = Expr[]
        bodys = Expr[]

        for T in SYMTYPE_VARIANTS
            isconcretetype(T) || continue
            push!(conds, :(arg isa $T))
            push!(bodys, :(Const{$T}(arg)))
        end

        expr = :()
        if !isempty(conds)
            root_cond, rest_conds = Iterators.peel(conds)
            root_body, rest_bodys = Iterators.peel(bodys)
            expr = Expr(:if, root_cond, root_body)
            cur_expr = expr
            for (cond, body) in zip(rest_conds, rest_bodys)
                global cur_expr
                new_chain = Expr(:elseif, cond, body)
                push!(cur_expr.args, new_chain)
                cur_expr = new_chain
            end
            push!(cur_expr.args, :(Const{typeof(arg)}(arg)::BasicSymbolic))
        end
        
        expr
    end)
end

Base.@nospecializeinfer function maybe_const(arg)
    @nospecialize arg
    arg isa BasicSymbolic ? arg : closest_const(arg)
end

Base.@nospecializeinfer function maybe_const(::Type{T}, arg) where {T}
    @nospecialize arg
    arg isa BasicSymbolic ? arg : Const{T}(arg)
end

function parse_args(args::Union{Tuple, AbstractVector})
    args isa ROArgsT && return parent(args)
    args isa ArgsT && return args
    _args = ArgsT()
    sizehint!(_args, length(args))
    for arg in args
        push!(_args, arg isa BasicSymbolic ? arg : closest_const(arg))
    end
    return _args::ArgsT
end

function unwrap_args(args)
    if any(x -> unwrap(x) !== x, args)
        map(unwrap, args)
    else
        args
    end
end

@inline function BSImpl.Const{T}(val; unsafe = false) where {T}
    props = ordered_override_properties(BSImpl.Const)
    var = BSImpl.Const{T}(val, props...)
    if !unsafe
        var = hashcons(var)
    end
    return var
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

@inline function BSImpl.Polyform{T}(poly::PolynomialT{T}; metadata = nothing, shape = default_shape(T), unsafe = false) where {T}
    vars = SmallV{BasicSymbolic}()
    pvars = MP.variables(poly)
    partial_polyvars = Vector{PolyVarT}()
    sizehint!(vars, length(pvars))
    sizehint!(partial_polyvars, length(pvars))
    @manually_scope COMPARE_FULL => true begin
        for pvar in pvars
            var = polyvar_to_basicsymbolic(pvar)
            push!(vars, var)
            push!(partial_polyvars, basicsymbolic_to_partial_polyvar(var))
        end
    end
    return BSImpl.Polyform{T}(poly, partial_polyvars, vars; metadata, shape, unsafe)
end

@inline function BSImpl.Polyform{T}(poly::PolynomialT{T}, partial_polyvars::Vector{PolyVarT}, vars::SmallV{BasicSymbolic}; metadata = nothing, shape = default_shape(T), unsafe = false) where {T}
    metadata = parse_metadata(metadata)
    props = ordered_override_properties(BSImpl.Polyform)
    var = BSImpl.Polyform{T}(poly, partial_polyvars, vars, metadata, shape, props...)
    if !unsafe
        var = hashcons(var)
    end
    return var
end

@inline function BSImpl.Div{T}(num, den, simplified::Bool; metadata = nothing, shape = default_shape(T), unsafe = false) where {T}
    metadata = parse_metadata(metadata)
    num = maybe_const(num)
    den = maybe_const(den)
    props = ordered_override_properties(BSImpl.Div)
    var = BSImpl.Div{T}(num, den, simplified, metadata, shape, props...)
    if !unsafe
        var = hashcons(var)
    end
    return var
end

struct Const{T} end
struct Sym{T} end
struct Term{T} end
struct Polyform{T} end
struct Div{T} end

function Const{T}(val) where {T}
    val = unwrap(val)
    val isa BasicSymbolic && return val
    BSImpl.Const{T}(convert(T, val))
end

Sym{T}(name; kw...) where {T} = BSImpl.Sym{T}(name; kw...)

function Term{T}(f, args; kw...) where {T}
    args = unwrap_args(args)
    BSImpl.Term{T}(f, args; kw...)
end

function Term(f, args; kw...)
    Term{_promote_symtype(f, args)}(f, args; kw...)
end

function Polyform{T}(poly::PolynomialT, args...; kw...) where {T}
    nterms = MP.nterms(poly)
    if iszero(nterms)
        return zero(T)
    elseif MP.isconstant(poly)
        return MP.leading_coefficient(poly)
    elseif isone(nterms)
        term = MP.terms(poly)[1]
        coeff = MP.coefficient(term)
        mono = MP.monomial(term)
        exps = MP.exponents(mono)
        nnz = count(!iszero, exps)
        if isone(coeff) && isone(nnz) 
            idx = findfirst(!iszero, exps)
            isone(exps[idx]) && return polyvar_to_basicsymbolic(MP.variables(mono)[idx])
        elseif isone(-coeff) && isone(nnz)
            idx = findfirst(!iszero, exps)
            if isone(exps[idx])
                pvars = MP.variables(poly)
                var = polyvar_to_basicsymbolic(pvars[idx])
                @match var begin
                    BSImpl.Term(; f, args) && if f === (+) end => begin
                        args = copy(parent(args))
                        map!(x -> coeff * x, args, args)
                        return BSImpl.Term(; f, args)
                    end
                    BSImpl.Polyform(;) => return -var
                    _ => nothing
                end
            end
        end
    end
    BSImpl.Polyform{T}(poly, args...; kw...)
end

Polyform(poly::PolynomialT{T}, args...; kw...) where {T} = Polyform{T}(poly, args...; kw...)

"""
    $(TYPEDSIGNATURES)

Create a generic division term. Does not assume anything about the division algebra beyond
the ability to check for zero and one elements (via [`_iszero`](@ref) and [`_isone`](@ref)).

If the numerator is zero or denominator is one, the numerator is returned.
"""
function Div{T}(n, d, simplified; kw...) where {T}
    n = unwrap_const(unwrap(n))
    d = unwrap_const(unwrap(d))
    # TODO: This used to return `zero(typeof(n))`, maybe there was a reason?
    _iszero(n) && return maybe_const(T, n)
    _isone(d) && return maybe_const(T, n)
    return BSImpl.Div{T}(n, d, simplified; kw...)
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

Create a division term specifically for the real or complex algebra. Performs additional
simplification and cancellation.
"""
function Div{T}(n, d, simplified; kw...) where {T <: Number}
    n = unwrap_const(unwrap(n))
    d = unwrap_const(unwrap(d))

    if !(T == SafeReal)
        n, d = quick_cancel(n, d)
    end
    n = unwrap_const(n)
    d = unwrap_const(d)

    _iszero(n) && return Const{T}(zero(typeof(n)))
    _isone(d) && return maybe_const(T, n)

    if isdiv(n) && isdiv(d)
        return Div{T}(n.num * d.den, n.den * d.num, simplified; kw...)
    elseif isdiv(n)
        return Div{T}(n.num, n.den * d, simplified; kw...)
    elseif isdiv(d)
        return Div{T}(n * d.den, d.num, simplified; kw...)
    end

    d isa Number && _isone(-d) && return maybe_const(T, -n)
    n isa Rat && d isa Rat && return Const{T}(n // d)

    n, d = simplify_coefficients(n, d)

    _isone(d) && return maybe_const(T, n)
    _isone(-d) && return maybe_const(T, -n)

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

function unwrap_const(x)
    isconst(x) ? x.val : x
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
    @nospecialize f
    if type === nothing
        T = _promote_symtype(f, args)
    else
        T = type
    end
    Term{T}(f, args)
end

function TermInterface.maketerm(::Type{T}, head, args, metadata) where {T<:BasicSymbolic}
    @nospecialize head
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

function basicsymbolic(f, args, ::Type{T}, metadata) where {T}
    @nospecialize f
    if f isa Symbol
        error("$f must not be a Symbol")
    end
    args = unwrap_args(args)
    if T === LiteralReal
        @goto FALLBACK
    elseif all(x->x isa Union{Number, BasicSymbolic{<:Number}}, args)
        if f === (+)
            res = add_worker(args)
            if metadata !== nothing && (isadd(res) || (isterm(res) && operation(res) == (+)))
                @set! res.metadata = metadata
            end
            return res
        elseif f === (*)
            res = mul_worker(args)
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
        Term{T}(f, args, metadata=metadata)
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

issafecanon(f, s) = true
function issafecanon(f, s::BasicSymbolic)
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
###  Pretty printing
###
const show_simplified = Ref(false)

isnegative(t::Real) = t < 0
function isnegative(t)
    if iscall(t) && operation(t) === (*)
        coeff = first(arguments(t))
        return isnegative(unwrap_const(coeff))
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
    @assert unwrap_const(args[1]) < 0
    Any[-unwrap_const(args[1]), args[2:end]...]
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
    base = unwrap_const(base)
    ex = unwrap_const(ex)
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

    arg1 = unwrap_const(args[1])
    arg2 = unwrap_const(args[2])
    minus = arg1 isa Number && arg1 == -1
    unit = arg1 isa Number && arg1 == 1

    paren_scalar = (arg1 isa Complex && !_iszero(imag(arg1))) ||
                   arg1 isa Rational ||
                   (arg1 isa Number && !isfinite(arg1))

    nostar = minus || unit ||
            (!paren_scalar && unwrap_const(arg1) isa Number && !(arg2 isa Number))

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
        v = unwrap_const(v)
        if v isa Complex
            printstyled(io, "("; color = :blue)
        end
        printstyled(io, v; color = :blue)
        if v isa Complex
            printstyled(io, ")"; color = :blue)
        end
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

(f::BasicSymbolic{<:FnType})(args...) = Term{promote_symtype(f, symtype.(args)...)}(f, SmallV{Any}(args))

function (f::BasicSymbolic)(args...)
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

function Base.show(io::IO, f::BasicSymbolic{<:FnType{X,Y}}) where {X,Y}
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
const SN = BasicSymbolic{<:Number}
# integration. Constructors of `Add, Mul, Pow...` from Base (+, *, ^, ...)

add_t(a::Number,b::Number) = promote_symtype(+, symtype(a), symtype(b))
add_t(a,b) = promote_symtype(+, symtype(a), symtype(b))
sub_t(a,b) = promote_symtype(-, symtype(a), symtype(b))
sub_t(a) = promote_symtype(-, symtype(a))

import Base: (+), (-), (*), (//), (/), (\), (^)

function +(a::SN, bs::SN...)
    add_worker((a, bs...))
end

function add_worker(terms)
    isempty(terms) && return 0
    if isone(length(terms))
        return only(terms)
    end
    # entries where `!issafecanon`
    unsafes = SmallV{Any}()
    a, bs = Iterators.peel(terms)
    T = symtype(a)
    for b in bs
        T = promote_symtype(+, T, symtype(b))
    end
    result = zeropoly(T)::PolynomialT
    for term in terms
        term = unwrap_const(unwrap(term))
        if !issafecanon(+, term)
            push!(unsafes, term)
            continue
        end
        @match term begin
            x::Number => begin
                # DynamicPolynomials will mutate number types if it can. SymbolicUtils
                # doesn't assume ownership of values passed to it, so we copy the ones
                # we need to.
                x = MA.copy_if_mutable(x)
                MA.operate!(+, result, x)
            end
            BSImpl.Polyform(; poly) => begin
                MA.operate!(+, result, poly)
            end
            x::BasicSymbolic => begin
                pvar = basicsymbolic_to_polyvar(x)
                MA.operate!(+, result, pvar)
            end
        end
    end
    nterms = MP.nterms(result)
    if any(iszero, MP.coefficients(result))
        mask = (!iszero).(MP.coefficients(result))
        result = PolynomialT{T}(MP.coefficients(result)[mask], MP.monomials(result)[mask])
    end
    if iszero(nterms) && isempty(unsafes)
        return zero(T)
    elseif iszero(nterms)
        return Term{T}(+, unsafes)
    elseif isempty(unsafes)
        return Polyform{T}(result)
    else
        push!(unsafes, Polyform{T}(result))
        # ensure `result` is always the first
        unsafes[1], unsafes[end] = unsafes[end], unsafes[1]
        return Term{T}(+, unsafes)
    end
end

function +(a::Number, b::SN, bs::SN...)
    return add_worker((a, b, bs...))
end

function +(a::SN, b::Number, bs::SN...)
    return +(b, a, bs...)
end

function -(a::SN)
    a = unwrap_const(a)
    a isa SN || return -a
    !issafecanon(*, a) && return term(-, a)
    T = sub_t(a)
    @match a begin
        BSImpl.Polyform(; poly, vars, partial_polyvars, shape) => begin
            result = copy(poly)
            MP.map_coefficients_to!(result, (-), poly; nonzero = true)
            Polyform{T}(result, partial_polyvars, vars; shape)
        end
        _ => (-1 * a)
    end
end

function -(a::SN, b::SN)
    (!issafecanon(+, a) || !issafecanon(*, b)) && return term(-, a, b)
    @match (a, b) begin
        (BSImpl.Polyform(; poly = poly1), BSImpl.Polyform(; poly = poly2)) => begin
            T = sub_t(a, b)
            return Polyform{T}(poly1 - poly2)
        end
        _ => return add_worker((a, -b))
    end
end

-(a::Number, b::SN) = a + (-b)
-(a::SN, b::Number) = a + (-b)


mul_t(a,b) = promote_symtype(*, symtype(a), symtype(b))
mul_t(a) = promote_symtype(*, symtype(a))

*(a::SN) = a

function _mul_worker!(num_coeff, den_coeff, num_dict, den_dict, term)
    @match term begin
        x::Number => (num_coeff[] *= x)
        BSImpl.Polyform(; poly, vars) && if polyform_variant(poly) != PolyformVariant.ADD end => begin
            pterm = only(MP.terms(poly))
            num_coeff[] *= MP.coefficient(pterm)
            mono = MP.monomial(pterm)
            for (i, exp) in enumerate(MP.exponents(mono))
                base = vars[i]
                if iscall(base) && operation(base) === ^
                    _base, _exp = arguments(base)
                    if _base isa BasicSymbolic && !(_exp isa BasicSymbolic)
                        base = _base
                        exp *= _exp
                    end
                end
                num_dict[base] = get(num_dict, base, 0) + exp
            end
        end
        BSImpl.Term(; f, args) && if f === (^) && args[1] isa BasicSymbolic && !(args[2] isa BasicSymbolic) end => begin
            base, exp = args
            num_dict[base] = get(num_dict, base, 0) + exp
        end
        BSImpl.Div(; num, den) => begin
            _mul_worker!(num_coeff, den_coeff, num_dict, den_dict, unwrap_const(num))
            _mul_worker!(den_coeff, num_coeff, den_dict, num_dict, unwrap_const(den))
        end
        x::BasicSymbolic => begin
            num_dict[x] = get(num_dict, x, 0) + 1
        end
    end
    return nothing
    # return (num_coeff, den_coeff)::Tuple{Number, Number}
end

function coeff_dict_to_term(::Type{T}, coeff, dict) where {T}
    isempty(dict) && return coeff[]::T
    if isone(coeff[]) && length(dict) == 1
        k, v = first(dict)
        return (k ^ v)
    end
    pvars = PolyVarT[]
    partial_pvars = PolyVarT[]
    vars = SmallV{BasicSymbolic}()
    exps = Int[]
    sizehint!(pvars, length(dict))
    sizehint!(partial_pvars, length(dict))
    sizehint!(vars, length(dict))
    sizehint!(exps, length(dict))
    for (k, v) in dict
        if !isinteger(v)
            k = Term{T}(^, ArgsT((k, v)))
            v = 1
        end
        push!(vars, k)
        push!(pvars, basicsymbolic_to_polyvar(k))
        push!(partial_pvars, basicsymbolic_to_partial_polyvar(k))
        push!(exps, Int(v))
    end

    N = length(pvars)
    if N == 2
        if pvars[1] < pvars[2]
            pvars[1], pvars[2] = pvars[2], pvars[1]
            partial_pvars[1], partial_pvars[2] = partial_pvars[2], partial_pvars[1]
            vars[1], vars[2] = vars[2], vars[1]
            exps[1], exps[2] = exps[2], exps[1]
        end
    elseif N > 2
        perm = sortperm(pvars; rev=true)
        pvars = pvars[perm]
        partial_pvars = partial_pvars[perm]
        vars = vars[perm]
        exps = exps[perm]
    end

    mvec = DP.MonomialVector{PolyVarOrder, MonomialOrder}(pvars, [exps])
    Polyform{T}(PolynomialT{T}(coeff, mvec), partial_pvars, vars)
end

function mul_worker(terms)
    length(terms) == 1 && return only(terms)
    a, bs = Iterators.peel(terms)
    a = unwrap(a)
    T = symtype(a)
    for b in bs
        T = promote_symtype(*, T, symtype(b))
    end
    mul_worker(T, terms)
end

function mul_worker(::Type{T}, terms) where {T}
    unsafes = SmallV{Any}()
    num_coeff = T[1]
    den_coeff = T[1]
    num_dict = Dict{BasicSymbolic, Any}()
    den_dict = Dict{BasicSymbolic, Any}()

    for term in terms
        term = unwrap_const(unwrap(term))
        if !issafecanon(*, term)
            push!(unsafes, term)
            continue
        end
        _mul_worker!(num_coeff, den_coeff, num_dict, den_dict, term)
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
    num = coeff_dict_to_term(T, num_coeff, num_dict)# ::Union{T, BasicSymbolic{T}}
    den = coeff_dict_to_term(T, den_coeff, den_dict)# ::Union{T, BasicSymbolic{T}}
    if !isempty(unsafes)
        push!(unsafes, num)
        # ensure `num` is always the first
        unsafes[1], unsafes[end] = unsafes[end], unsafes[1]
        num = Term{T}(*, unsafes)
    end

    return Div{T}(num, den, false)
end

function *(a::SN, b::SN)
    mul_worker(mul_t(a, b), (a, b))
end

function *(a::Number, b::SN)
    mul_worker(mul_t(a, b), (a, b))
end

###
### Div
###

function /(a::Union{SN,Number}, b::SN)
    if isconst(a) || isconst(b)
        return unwrap_const(a) / unwrap_const(b)
    end
    Div{promote_symtype(/, symtype(a), symtype(b))}(a, b, false)
end

*(a::SN, b::Number) = b * a

\(a::SN, b::Union{Number, SN}) = b / a

\(a::Number, b::SN) = b / a

/(a::SN, b::Number) = (isone(abs(b)) ? b : (b isa Integer ? 1//b : inv(b))) * a

//(a::Union{SN, Number}, b::SN) = a / b

//(a::SN, b::Number) = (one(b) // b) * a


###
### Pow
###

function ^(a::SN, b)
    isconst(a) && return ^(unwrap_const(a), b)
    a = unwrap_const(a)
    b = unwrap_const(unwrap(b))
    T = promote_symtype(^, symtype(a), symtype(b))
    !issafecanon(^, a, b) && return Term{T}(^, ArgsT((a, maybe_const(b))))
    if b isa Number
        iszero(b) && return 1
        isone(b) && return a
    end
    if b isa Real && b < 0
        return Div{T}(1, a ^ (-b), false)
    end
    if b isa Number && iscall(a) && operation(a) === (^) && isconst(arguments(a)[2]) && unwrap_const(arguments(a)[2]) isa Number
        base, exp = arguments(a)
        exp = unwrap_const(exp)
        return base ^ (exp * b)
    end
    @match a begin
        BSImpl.Div(; num, den) => return BSImpl.Div{T}(num ^ b, den ^ b, false)
        _ => nothing
    end
    if b isa Number && isinteger(b)
        @match a begin
            BSImpl.Polyform(; poly, partial_polyvars, vars) && if polyform_variant(poly) != PolyformVariant.ADD end => begin
                poly = MP.polynomial(poly ^ Int(b), T)
                return Polyform{T}(poly, partial_polyvars, vars)
            end
            _ => return Polyform{T}(MP.polynomial(basicsymbolic_to_polyvar(a) ^ Int(b), T))
        end
    end
    return BSImpl.Term{T}(^, ArgsT((a, maybe_const(b))))
end

^(a::Number, b::SN) = Term{promote_symtype(^, symtype(a), symtype(b))}(^, ArgsT((closest_const(a), b)))
