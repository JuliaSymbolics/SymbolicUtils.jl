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
const ShapeVecT = SmallV{UnitRange{Int}}
const ShapeT = Union{Unknown, ShapeVecT}
const IdentT = Union{Tuple{UInt, IDType}, Tuple{Nothing, Nothing}}
const PolyVarOrder = MP.Graded{MP.Reverse{MP.InverseLexOrder}}
const ExamplePolyVar = only(DP.@polyvar __DUMMY__ monomial_order=PolyVarOrder)
const PolyVarT = typeof(ExamplePolyVar)
const PolynomialT{T} = DP.Polynomial{DP.Commutative{DP.CreationOrder}, PolyVarOrder, T}

function zeropoly(::Type{T}) where {T}
    mv = DP.MonomialVector{DP.Commutative{DP.CreationOrder}, PolyVarOrder}()
    PolynomialT{T}(T[], mv)
end

function onepoly(::Type{T}) where {T}
    V = DP.Commutative{DP.CreationOrder}
    mv = DP.MonomialVector{V, PolyVarOrder}(DP.Variable{V, PolyVarOrder}[], [Int[]])
    PolynomialT{T}(T[one(T)], mv)
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
    struct Polyform
        # polynomial in terms of full hashed variables
        const poly::PolynomialT{T}
        # corresponding to poly.x.vars, the partially hashed variables
        const partial_polyvars::Vector{PolyVarT}
        # corresponding to poly.x.vars, the BasicSymbolic variables
        const vars::SmallV{BasicSymbolicImpl.Type}
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
end

const BSImpl = BasicSymbolicImpl
const BasicSymbolic = BSImpl.Type

const POLYVAR_LOCK = ReadWriteLock()
# NOTE: All of these are accessed via POLYVAR_LOCK
const BS_TO_PVAR = WeakKeyDict{BasicSymbolic, PolyVarT}()
const BS_TO_PARTIAL_PVAR = WeakKeyDict{BasicSymbolic, PolyVarT}()
const PVAR_TO_BS = Dict{Symbol, WeakRef}()
const PARTIAL_PVARS = Set{Symbol}()

# TODO: manage scopes better here
function basicsymbolic_to_polyvar(x::BasicSymbolic)::PolyVarT
    pvar = partial_pvar = name = partial_name = nothing
    @manually_scope COMPARE_FULL => true begin
        @readlock POLYVAR_LOCK begin
            pvar = get(BS_TO_PVAR, x, nothing)

            if pvar !== nothing
                return pvar
            end

            inner_name = @match x begin
                BSImpl.Sym(; name) => name
                _ => nameof(operation(x))
            end
            name = Symbol(inner_name, :_, hash(x))
            while haskey(PVAR_TO_BS, name)
                # `cache` didn't have a mapping for `x`, so `rev_cache` cannot have
                # a valid mapping for the polyvar (name)
                name = Symbol(name, :_)
            end

            pvar = MP.similar_variable(ExamplePolyVar, name)
            @manually_scope COMPARE_FULL => false begin
                # do the same thing, but for the partial hash
                partial_name = Symbol(inner_name, :_, hash(x))
            end true
            while partial_name in PARTIAL_PVARS
                # `cache` didn't have a mapping for `x`, so `rev_cache` cannot have
                # a valid mapping for the polyvar (name)
                partial_name = Symbol(partial_name, :_)
            end
            partial_pvar = MP.similar_variable(ExamplePolyVar, partial_name)
        end
        @lock POLYVAR_LOCK begin
            BS_TO_PARTIAL_PVAR[x] = partial_pvar
            BS_TO_PVAR[x] = pvar
            PVAR_TO_BS[name] = WeakRef(x)
            push!(PARTIAL_PVARS, partial_name)
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
        ::Type{<:BSImpl.Sym} => (; id = (nothing, nothing), hash2 = 0)
        ::Type{<:BSImpl.Polyform} => (; id = (nothing, nothing), hash = 0, hash2 = 0)
        ::Type{<:BSImpl.Term} => (; id = (nothing, nothing), hash = 0, hash2 = 0)
        ::Type{<:BSImpl.Div} => (; id = (nothing, nothing), hash2 = 0)
        _ => throw(UnimplementedForVariantError(override_properties, obj))
    end
end

function ordered_override_properties(obj::Type{<:BSImpl.Variant})
    @match obj begin
        ::Type{<:BSImpl.Sym} => (0, (nothing, nothing))
        ::Type{<:BSImpl.Term} => (0, 0, (nothing, nothing))
        ::Type{<:BSImpl.Polyform} => (ArgsT(), 0, 0, (nothing, nothing))
        ::Type{<:BSImpl.Div} => (0, (nothing, nothing))
        _ => throw(UnimplementedForVariantError(override_properties, obj))
    end
end

function ConstructionBase.getproperties(obj::BSImpl.Type)
    @match obj begin
        BSImpl.Sym(; name, metadata, hash2, shape, id) => (; name, metadata, hash2, shape, id)
        BSImpl.Term(; f, args, metadata, hash, hash2, shape, id) => (; f, args, metadata, hash, hash2, shape, id)
        BSImpl.Polyform(; poly, partial_polyvars, vars, metadata, shape, args, hash, hash2, id) => (; poly, partial_polyvars, vars, metadata, shape, args, hash, hash2, id)
        BSImpl.Div(; num, den, simplified, metadata, hash2, shape, id) => (; num, den, simplified, metadata, hash2, shape, id)
    end
end

function ConstructionBase.setproperties(obj::BSImpl.Type{T}, patch::NamedTuple)::BSImpl.Type{T} where {T}
    props = getproperties(obj)
    overrides = override_properties(obj)
    # We only want to invalidate `args` if we're updating `coeff` or `dict`.
    if ispolyform(obj)
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

# We're returning a function pointer
@inline function TermInterface.operation(x::BSImpl.Type)
    @match x begin
        # BSImpl.Const(_) => throw(ArgumentError("`Const` does not have an operation."))
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

function TermInterface.arguments(x::BSImpl.Type)::ROArgsT
    @match x begin
        # BSImpl.Const(_) => throw(ArgumentError("`Const` does not have arguments."))
        BSImpl.Sym(_) => throw(ArgumentError("`Sym` does not have arguments."))
        BSImpl.Term(; args) => ROArgsT(args)
        BSImpl.Polyform(; poly, partial_polyvars, vars, args, shape) => begin
            T = symtype(x)
            isempty(args) || return ROArgsT(args)
            @match polyform_variant(poly) begin
                PolyformVariant.ADD => begin
                    for term in MP.terms(poly)
                        coeff = MP.coefficient(term)
                        mono = MP.monomial(term)
                        exps = MP.exponents(mono)
                        if MP.isconstant(term)
                            push!(args, coeff)
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
                        push!(args, coeff)
                    end
                    for (var, pow) in zip(vars, MP.exponents(mono))
                        iszero(pow) && continue
                        if isone(pow)
                            push!(args, var)
                        else
                            push!(args, Term{T}(^, ArgsT((var, pow))))
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
                    push!(args, pow)
                end
            end
            return ROArgsT(args)
        end
        BSImpl.Div(num, den) => ROArgsT(ArgsT((num, den)))
        _ => throw(UnimplementedForVariantError(arguments, MData.variant_type(x)))
    end
end

function isexpr(s::BSImpl.Type)
    !MData.isa_variant(s, BSImpl.Sym) # && !MData.isa_variant(s.inner, BSImpl.Const)
end
iscall(s::BSImpl.Type) = isexpr(s)

# isconst(x::BSImpl.Type) = MData.isa_variant(x, BSImpl.Const)
isconst(x) = false
issym(x::BSImpl.Type) = MData.isa_variant(x, BSImpl.Sym)
isterm(x::BSImpl.Type) = MData.isa_variant(x, BSImpl.Term)
ispolyform(x::BSImpl.Type) = MData.isa_variant(x, BSImpl.Polyform)
isadd(x::BSImpl.Type) = ispolyform(x) && polyform_variant(x) == PolyformVariant.ADD
ismul(x::BSImpl.Type) = ispolyform(x) && polyform_variant(x) == PolyformVariant.MUL
isdiv(x::BSImpl.Type) = MData.isa_variant(x, BSImpl.Div)
ispow(x::BSImpl.Type) = ispolyform(x) && polyform_variant(x) == PolyformVariant.POW

for fname in [:issym, :isterm, :ispolyform, :isadd, :ismul, :isdiv, :ispow]
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
    if full && partial
        partial = isequal(metadata(a), metadata(b))
    end
    return partial
end

function Base.isequal(a::BSImpl.Type, b::BSImpl.Type)
    isequal_bsimpl(a, b, COMPARE_FULL[])
end

Base.isequal(a::BSImpl.Type, b::WeakRef) = isequal(a, b.value)
Base.isequal(a::WeakRef, b::BSImpl.Type) = isequal(a.value, b)

# const CONST_SALT = 0x194813feb8a8c83d % UInt
const SYM_SALT = 0x4de7d7c66d41da43 % UInt
const ADD_SALT = 0xaddaddaddaddadda % UInt
const MUL_SALT = 0xaaaaaaaaaaaaaaaa % UInt
const DIV_SALT = 0x334b218e73bbba53 % UInt
const POW_SALT = 0x2b55b97a6efb080c % UInt
const PLY_SALT = 0x36ee940e7fa431a3 % UInt

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
        BSImpl.Polyform(; poly, partial_polyvars, shape, hash) => begin
            if full
                Base.hash(swap_polynomial_vars(poly, partial_polyvars), Base.hash(shape, h))
            else
                if iszero(hash)
                    s.hash = Base.hash(poly, Base.hash(shape, h))
                else
                    hash
                end
            end
        end
        BSImpl.Div(; num, den) => begin
            hash_anyscalar(num, hash_anyscalar(den, h, full), full) ⊻ DIV_SALT
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
        if k.id === (nothing, nothing)
            k.id = generate_id()
        end
        return k
    end true
end

# function BSImpl.Const{T}(val::T) where {T}
#     hashcons(BSImpl.Const{T}(; val, override_properties(BSImpl.Const{T})...))
# end

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
    num = maybe_integer(parse_maybe_symbolic(num))
    den = maybe_integer(parse_maybe_symbolic(den))
    props = ordered_override_properties(BSImpl.Div)
    var = BSImpl.Div{T}(num, den, simplified, metadata, shape, props...)
    if !unsafe
        var = hashcons(var)
    end
    return var
end

# struct Const{T} end
struct Sym{T} end
struct Term{T} end
struct Polyform{T} end
struct Div{T} end

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

function Polyform{T}(poly::PolynomialT, args...; kw...) where {T}
    nterms = MP.nterms(poly)
    if MP.isconstant(poly)
        return MP.leading_coefficient(poly)
    elseif isone(nterms)
        term = MP.terms(poly)[1]
        coeff = MP.coefficient(term)
        mono = MP.monomial(term)
        exps = MP.exponents(mono)
        if isone(coeff) && isone(count(!iszero, exps)) 
            idx = findfirst(!iszero, exps)
            isone(exps[idx]) && return polyvar_to_basicsymbolic(MP.variables(mono)[idx])
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

function unwrap_const(x)
    x
    # isconst(x) ? x.val : x
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
    $(TYPEDSIGNATURES)
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

add_t(a::Number,b::Number) = promote_symtype(+, symtype(a), symtype(b))
add_t(a,b) = promote_symtype(+, symtype(a), symtype(b))
sub_t(a,b) = promote_symtype(-, symtype(a), symtype(b))
sub_t(a) = promote_symtype(-, symtype(a))

import Base: (+), (-), (*), (//), (/), (\), (^)

function +(a::SN, bs::SN...)
    add_worker((a, bs...))
end

function add_worker(terms)
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
    result = zeropoly(T)
    for term in terms
        term = unwrap(term)
        if !issafecanon(+, term)
            push!(unsafes, term)
            continue
        end
        @match term begin
            x::Number => MA.operate!(+, result, x)
            BSImpl.Polyform(; poly) => MA.operate!(+, result, poly)
            x::BasicSymbolic => MA.operate!(+, result, basicsymbolic_to_polyvar(x))
        end
    end
    nterms = MP.nterms(result)
    if iszero(nterms) && isempty(unsafes)
        return zero(T)
    elseif iszero(nterms)
        return Term{T}(+, unsafes)
    elseif isempty(unsafes)
        return Polyform{T}(result)
    else
        push!(unsafes, Polyform{T}(result))
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
            poly2 = MP.map_coefficients((-), poly2)
            MA.operate!(+, poly2, poly1)
            return Polyform{sub_t(a, b)}(poly2)
        end
        _ => return add_worker((a, -b))
    end
end

-(a::Number, b::SN) = a + (-b)
-(a::SN, b::Number) = a + (-b)


mul_t(a,b) = promote_symtype(*, symtype(a), symtype(b))
mul_t(a) = promote_symtype(*, symtype(a))

*(a::SN) = a

struct MultipliedPolynomialPostprocessor
    base_occurrences::Dict{BasicSymbolic, BitSet}
    var_exponents::Vector{Real}
    monomial::(typeof(MP.monomial(ExamplePolyVar)))
    varsbuf::Vector{BasicSymbolic}
    var_to_idx::Dict{BasicSymbolic, Int}
end

MultipliedPolynomialPostprocessor() = MultipliedPolynomialPostprocessor(Dict(), Real[], MP.monomial(ExamplePolyVar), BasicSymbolic[], Dict())

const CACHED_MPP = TaskLocalValue{MultipliedPolynomialPostprocessor}(MultipliedPolynomialPostprocessor)

function (mpp::MultipliedPolynomialPostprocessor)(poly::PolynomialT, ::Type{T}) where {T}
    pvars = MP.variables(poly)
    vars = mpp.varsbuf
    empty!(vars)
    sizehint!(vars, length(pvars))
    var_to_idx = mpp.var_to_idx
    empty!(var_to_idx)
    base_occurrences = mpp.base_occurrences
    empty!(base_occurrences)
    var_exponents = mpp.var_exponents
    empty!(var_exponents)
    for (i, pvar) in enumerate(pvars)
        var = polyvar_to_basicsymbolic(pvar)
        push!(vars, var)
        var_to_idx[var] = i
        if iscall(var) && operation(var) === (^)
            base, exp = arguments(var)
            if !(exp isa Real)
                base, exp = var, 1
            end
        else
            base, exp = var, 1
        end
        push!(var_exponents, exp)
        push!(get!(BitSet, base_occurrences, base), i)
    end

    result = zero(PolynomialT{T})
    monomial_buffer = mpp.monomial
    for term in MP.terms(poly)
        coeff = MP.coefficient(term)
        mono = MP.monomial(term)
        exps = MP.exponents(mono)

        new_mono = MP.constant_monomial(result)
        for (base, mask) in base_occurrences
            exp = sum(mask) do i
                exps[i] * var_exponents[i]
            end
            if isinteger(exp)
                mbase = basicsymbolic_to_polyvar(base)
                mexp = Int(exp)
            else
                mbase = basicsymbolic_to_polyvar(Term{T}(^, ArgsT((base, exp))))
                mexp = 1
            end
            # cheat to avoid allocations
            MP.variables(monomial_buffer)[] = mbase
            MP.exponents(monomial_buffer)[] = mexp
            MA.operate!(*, new_mono, monomial_buffer)
        end
        new_term = MP.Term{T, typeof(new_mono)}(coeff, new_mono)
        MA.operate!(+, result, new_term)
    end

    return result
end

postprocessed_multiplied_polynomial(args...) = CACHED_MPP[](args...)

function _mul_worker!(num_poly, den_poly, term)
    @match term begin
        x::Number => MA.operate!(*, num_poly, x)
        BSImpl.Polyform(; poly) && if polyform_variant(poly) == PolyformVariant.MUL end => begin
            MA.operate!(*, num_poly, poly)
        end
        BSImpl.Div(; num, den) => begin
            if den_poly === nothing
                den_poly = one(PolynomialT{T})
            end
            num_poly, den_poly = _mul_worker!(num_poly, den_poly, num)
            den_poly, num_poly = _mul_worker!(den_poly, num_poly, den)
        end
        _ => MA.operate!(*, num_poly, basicsymbolic_to_polyvar(term))
    end

    return num_poly, den_poly
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
    num_poly = one(PolynomialT{T})
    den_poly = nothing
    for term in terms
        if !issafecanon(*, term)
            push!(unsafes, term)
            continue
        end
        num_poly, den_poly = _mul_worker!(num_poly, den_poly, term)
    end
    num = Polyform{T}(postprocessed_multiplied_polynomial(num_poly, T))
    if !isempty(unsafes)
        push!(unsafes, num)
        num = Term{T}(*, unsafes)
    end
    if den_poly === nothing
        den = one(T)
    else
        den = Polyform{T}(postprocessed_multiplied_polynomial(den_poly, T))
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
    T = promote_symtype(^, symtype(a), symtype(b))
    !issafecanon(^, a, b) && return Term{T}(^, ArgsT((a, b)))
    if b isa Number && iszero(b)
        # fast path
        return 1
    end
    if b isa Real && b < 0
        return Div{T}(1, a ^ (-b), false)
    end
    @match a begin
        BSImpl.Div(; num, den) => return BSImpl.Div{T}(num ^ b, den ^ b, false)
        _ => nothing
    end
    if isinteger(b)
        @match a begin
            BSImpl.Sym(;) => return BSImpl.Polyform{T}(MP.polynomial(basicsymbolic_to_polyvar(a) ^ Int(b), T))
            BSImpl.Polyform(; poly, partial_polyvars, vars) && if polyform_variant(poly) != PolyformVariant.ADD end => begin
                poly = MP.polynomial(poly ^ Int(b), T)
                return Polyform{T}(poly, partial_polyvars, vars)
            end
        end
    end
    return BSImpl.Term{T}(^, ArgsT((a, b)))
end

^(a::Number, b::SN) = Term{promote_symtype(^, symtype(a), symtype(b))}(^, ArgsT((a, b)))
