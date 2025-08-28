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

ordered_override_properties(::Type{<:BSImpl.Const}) = ((nothing, nothing),)
ordered_override_properties(::Type{<:BSImpl.Sym}) = (0, (nothing, nothing))
ordered_override_properties(::Type{<:BSImpl.Term}) = (0, 0, (nothing, nothing))
ordered_override_properties(::Type{BSImpl.Polyform{T}}) where {T} = (ArgsT{T}(), 0, 0, (nothing, nothing))
ordered_override_properties(::Type{<:BSImpl.Div}) = (0, (nothing, nothing))

function ConstructionBase.getproperties(obj::BSImpl.Type)
    @match obj begin
        BSImpl.Const(; val, id) => (; val, id)
        BSImpl.Sym(; name, metadata, hash2, shape, type, id) => (; name, metadata, hash2, shape, type, id)
        BSImpl.Term(; f, args, metadata, hash, hash2, shape, type, id) => (; f, args, metadata, hash, hash2, shape, type, id)
        BSImpl.Polyform(; poly, partial_polyvars, vars, metadata, shape, type, args, hash, hash2, id) => (; poly, partial_polyvars, vars, metadata, shape, type, args, hash, hash2, id)
        BSImpl.Div(; num, den, simplified, metadata, hash2, shape, type, id) => (; num, den, simplified, metadata, hash2, shape, type, id)
    end
end

function ConstructionBase.setproperties(obj::BSImpl.Type{T}, patch::NamedTuple) where {T}
    props = getproperties(obj)
    overrides = override_properties(obj)
    # We only want to invalidate `args` if we're updating `coeff` or `dict`.
    if ispolyform(obj)
        extras = (; args = ArgsT{T}())
    else
        extras = (;)
    end
    hashcons(MData.variant_type(obj)(; props..., patch..., overrides..., extras...)::BasicSymbolic{T})
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

# We're returning a function pointer
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

const COMPARE_FULL = TaskLocalValue{Bool}(Returns(false))

function swap_polynomial_vars(poly::PolynomialT, new_vars::Vector{PolyVarT})
    typeof(poly)(MP.coefficients(poly), DP.MonomialVector(new_vars, MP.monomials(poly).Z))
end

function swap_polynomial_vars(_::PolyVarT, new_vars::Vector{PolyVarT})
    MP.polynomial(only(new_vars), PolyCoeffT)
end

isequal_bsimpl(::BSImpl.Type, ::BSImpl.Type, ::Bool) = false

function isequal_bsimpl(a::BSImpl.Type{T}, b::BSImpl.Type{T}, full::Bool) where {T}
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
            isequal(v1, v2)::Bool && (!full || typeof(v1) == typeof(v2))
        end
        (BSImpl.Sym(; name = n1, shape = s1, type = t1), BSImpl.Sym(; name = n2, shape = s2, type = t2)) => begin
            n1 === n2 && s1 == s2 && t1 === t2
        end
        (BSImpl.Term(; f = f1, args = args1, shape = s1, type = t1), BSImpl.Term(; f = f2, args = args2, shape = s2, type = t2)) => begin
            isequal(f1, f2)::Bool && isequal(args1, args2) && s1 == s2 && t1 === t2
        end
        (BSImpl.Polyform(; poly = p1, partial_polyvars = part1, shape = s1, type = t1), BSImpl.Polyform(; poly = p2, partial_polyvars = part2, shape = s2, type = t2)) => begin
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
            end && t1 === t2
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

const CONST_SALT = 0x194813feb8a8c83d % UInt
const SYM_SALT = 0x4de7d7c66d41da43 % UInt
const ADD_SALT = 0xaddaddaddaddadda % UInt
const MUL_SALT = 0xaaaaaaaaaaaaaaaa % UInt
const DIV_SALT = 0x334b218e73bbba53 % UInt
const POW_SALT = 0x2b55b97a6efb080c % UInt
const PLY_SALT = 0x36ee940e7fa431a3 % UInt

function hash_bsimpl(s::BSImpl.Type{T}, h::UInt, full) where {T}
    if !iszero(h)
        return hash(hash_bsimpl(s, zero(h), full), h)::UInt
    end
    h = hash(T, h)
    @match s begin
        BSImpl.Const(; val) => begin
            h = hash(val, h)::UInt
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
        BSImpl.Sym(; name, shape, type) => begin
            h = Base.hash(name, h)
            h = Base.hash(shape, h)
            h = Base.hash(type, h)
            h ⊻ SYM_SALT
        end
        BSImpl.Term(; f, args, shape, hash, type) => begin
            # use/update cached hash
            if iszero(hash)
                hash = s.hash = Base.hash(f, Base.hash(args, Base.hash(shape, Base.hash(type, h))))::UInt
            else
                hash
            end
        end
        BSImpl.Polyform(; poly, partial_polyvars, shape, hash, type) => begin
            if full
                Base.hash(poly, Base.hash(shape, Base.hash(type, h)))
            else
                if iszero(hash)
                    hash = s.hash = Base.hash(swap_polynomial_vars(poly, partial_polyvars), Base.hash(shape, Base.hash(type, h)))
                else
                    hash
                end
            end
        end
        BSImpl.Div(; num, den, type) => begin
            Base.hash(num, Base.hash(den, Base.hash(type, h))) ⊻ DIV_SALT
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

Base.nameof(s::BasicSymbolic) = issym(s) ? s.name : error("Non-Sym BasicSymbolic doesn't have a name")

###
### Constructors
###

# TODO: split into 3 caches based on `SymVariant`
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

@inline BSImpl.Const{T}(val::BasicSymbolic{T}; kw...) where {T} = val
@inline function BSImpl.Const{T}(val::BasicSymbolic{V}; kw...) where {T, V}
    error("Cannot construct `BasicSymbolic{$T}` from `BasicSymbolic{$V}`.")
end

@inline function BSImpl.Const{T}(val; unsafe = false) where {T}
    props = ordered_override_properties(BSImpl.Const)
    var = BSImpl.Const{T}(val, props...)
    if !unsafe
        var = hashcons(var)
    end
    return var
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

@inline function BSImpl.Polyform{T}(poly::PolynomialT; metadata = nothing, type, shape = default_shape(type), unsafe = false) where {T}
    vars = SmallV{BasicSymbolic{T}}()
    pvars = MP.variables(poly)
    partial_polyvars = Vector{PolyVarT}()
    sizehint!(vars, length(pvars))
    sizehint!(partial_polyvars, length(pvars))
    @manually_scope COMPARE_FULL => true begin
        for pvar in pvars
            var = polyvar_to_basicsymbolic(pvar)::BasicSymbolic{T}
            push!(vars, var)
            push!(partial_polyvars, basicsymbolic_to_partial_polyvar(var))
        end
    end
    return BSImpl.Polyform{T}(poly, partial_polyvars, vars; metadata, shape, type, unsafe)
end

@inline function BSImpl.Polyform{T}(poly::PolynomialT, partial_polyvars::Vector{PolyVarT}, vars::SmallV{BasicSymbolic{T}}; metadata = nothing, type, shape = default_shape(type), unsafe = false) where {T}
    metadata = parse_metadata(metadata)
    props = ordered_override_properties(BSImpl.Polyform{T})
    var = BSImpl.Polyform{T}(poly, partial_polyvars, vars, metadata, shape, type, props...)
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
struct Polyform{T} end
struct Div{T} end

@inline Const{T}(val; kw...) where {T} = BSImpl.Const{T}(val; kw...)

@inline Sym{T}(name; kw...) where {T} = BSImpl.Sym{T}(name; kw...)

@inline function Term{T}(f, args; type = _promote_symtype(f, args), kw...) where {T}
    args = unwrap_args(args)
    BSImpl.Term{T}(f, args; type, kw...)
end

function Polyform{T}(poly::PolynomialT, args...; kw...) where {T}
    nterms = MP.nterms(poly)
    if iszero(nterms)
        return Const{T}(0)
    elseif MP.isconstant(poly)
        return Const{T}(MP.leading_coefficient(poly))
    elseif isone(nterms)
        term = MP.terms(poly)[1]
        coeff = MP.coefficient(term)
        mono = MP.monomial(term)
        exps = MP.exponents(mono)
        nnz = count(!iszero, exps)
        if isone(coeff) && isone(nnz)
            idx = findfirst(!iszero, exps)
            isone(exps[idx]) && return polyvar_to_basicsymbolic(MP.variables(mono)[idx])::BasicSymbolic{T}
        elseif isone(-coeff) && isone(nnz)
            idx = findfirst(!iszero, exps)
            if isone(exps[idx])
                pvars = MP.variables(poly)
                var = polyvar_to_basicsymbolic(pvars[idx])::BasicSymbolic{T}
                @match var begin
                    BSImpl.Term(; f, args) && if f === (+) end => begin
                        args = copy(args)
                        map!(x -> coeff * x, args, args)
                        return BSImpl.Term{T}(; f, args)
                    end
                    BSImpl.Polyform(;) => return -var
                    _ => nothing
                end
            end
        end
    end
    BSImpl.Polyform{T}(poly, args...; kw...)
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
    end

    if !(T === SafeReal)
        n, d = quick_cancel(Const{T}(n), Const{T}(d))
    end
    n = unwrap_const(n)
    d = unwrap_const(d)

    _iszero(n) && return Const{T}(n)
    _isone(d) && return Const{T}(n)

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

function unwrap_const(x::BasicSymbolic)
    isconst(x) ? x.val : x
end
unwrap_const(x) = x

"""
    $(TYPEDSIGNATURES)
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

function getmetadata(s::BasicSymbolic, ctx)
    md = metadata(s)
    if md isa AbstractDict
        md[ctx]
    else
        throw(ArgumentError("$s does not have metadata for $ctx"))
    end
end

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
    if vartype(t) === TreeReal
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

function (f::BasicSymbolic{T})(args...) where {T}
    symtype(f) <: FnType || error("Sym $f is not callable. " *
          "Use @syms $f(var1, var2,...) to create it as a callable.")
    Term{T}(f, args; type = promote_symtype(f, symtype.(args)...))
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
    _vartype = SymReal
    if Meta.isexpr(xs[end], :(=))
        x = xs[end]
        key, val = x.args
        @assert key == :vartype
        if val == :SymReal
            _vartype = SymReal
        elseif val == :SafeReal
            _vartype = SafeReal
        elseif val == :TreeReal
            _vartype = TreeReal
        else
            error("Invalid vartype $val")
        end
        xs = Base.front(xs)
    end
    defs = map(xs) do x
        nt = _name_type(x)
        n, t = nt.name, nt.type
        T = esc(t)
        :($(esc(n)) = Sym{$_vartype}($(Expr(:quote, n)); type = $T))
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
const NonTreeSym = Union{BasicSymbolic{SymReal}, BasicSymbolic{SafeReal}}
# integration. Constructors of `Add, Mul, Pow...` from Base (+, *, ^, ...)

import Base: (+), (-), (*), (//), (/), (\), (^)

function +(x::T...) where {T <: NonTreeSym}
    if !all(y -> symtype(y) <: Number, x)
        throw(MethodError(+, x))
    end
    add_worker(vartype(T), x)
end

function add_worker(::Type{T}, terms) where {T <: Union{SymReal, SafeReal}}
    isempty(terms) && return Const{T}(0)
    if isone(length(terms))
        return Const{T}(only(terms))
    end
    # entries where `!issafecanon`
    unsafes = ArgsT{T}()
    a, bs = Iterators.peel(terms)
    type::TypeT = symtype(a)
    for b in bs
        type = promote_symtype(+, type, symtype(b))
    end
    result = zeropoly()
    for term in terms
        term = unwrap_const(unwrap(term))
        if !issafecanon(+, term)
            push!(unsafes, Const{T}(term))
            continue
        end
        if term isa BasicSymbolic{T}
            @match term begin
                BSImpl.Polyform(; poly) => begin
                    MA.operate!(+, result, poly)
                end
                x => begin
                    pvar = basicsymbolic_to_polyvar(x)
                    MA.operate!(+, result, pvar)
                end
            end
        elseif term isa BasicSymbolic
            error("Cannot operate on symbolics with different vartypes. Found `$T` and `$(vartype(x))`.")
        else
            # DynamicPolynomials will mutate number types if it can. SymbolicUtils
            # doesn't assume ownership of values passed to it, so we copy the ones
            # we need to.
            x = MA.copy_if_mutable(term)
            MA.operate!(+, result, x)
        end
    end
    nterms = MP.nterms(result)
    if any(iszero, MP.coefficients(result))
        mask = (!iszero).(MP.coefficients(result))
        result = PolynomialT(MP.coefficients(result)[mask], MP.monomials(result)[mask])
    end
    if iszero(nterms) && isempty(unsafes)
        return Const{T}(0)
    elseif iszero(nterms)
        return Term{T}(+, unsafes; type)
    elseif isempty(unsafes)
        return Polyform{T}(result; type)
    else
        push!(unsafes, Polyform{T}(result; type))
        # ensure `result` is always the first
        unsafes[1], unsafes[end] = unsafes[end], unsafes[1]
        return Term{T}(+, unsafes; type)
    end
end

function +(a::Number, b::T, bs::T...) where {T <: NonTreeSym}
    if !all(y -> symtype(y) <: Number, bs) || !(symtype(b) <: Number) || !(symtype(a) <: Number)
        throw(MethodError(+, symtype.((a, b, bs...))))
    end
    @assert !(unwrap(a) isa BasicSymbolic{TreeReal})
    return add_worker(vartype(T), (a, b, bs...))
end

function +(a::T, b::Number, bs::T...) where {T <: NonTreeSym}
    if !all(y -> symtype(y) <: Number, bs) || !(symtype(b) <: Number) || !(symtype(a) <: Number)
        throw(MethodError(+, symtype.((a, b, bs...))))
    end
    @assert !(unwrap(b) isa BasicSymbolic{TreeReal})
    return +(b, a, bs...)
end

function -(a::BasicSymbolic{T}) where {T}
    if !(symtype(a) <: Number)
        throw(MethodError(-, (symtype(a),)))
    end
    @match a begin
        BSImpl.Const(; val) => Const{T}(-val)
        _ => nothing
    end
    type::TypeT = promote_symtype(-, symtype(a))
    !issafecanon(*, a) && return Term{T}(-, ArgsT{T}((a,)); type)
    @match a begin
        BSImpl.Polyform(; poly, vars, partial_polyvars, shape, type) => begin
            result = copy(poly)
            MP.map_coefficients_to!(result, (-), poly; nonzero = true)
            Polyform{T}(result, partial_polyvars, vars; shape, type)
        end
        _ => (-1 * a)
    end
end

function -(a::S, b::S) where {S <: NonTreeSym}
    if !(symtype(a) <: Number) || !(symtype(b) <: Number)
        throw(MethodError(-, (a, b)))
    end
    T = vartype(S)
    type::TypeT = promote_symtype(-, symtype(a), symtype(b))
    if !issafecanon(+, a) || !issafecanon(*, b)
        return Term{T}(-, ArgsT{T}((a, b)); type)
    end
    @match (a, b) begin
        (BSImpl.Const(; val = val1), BSImpl.Const(; val = val2)) => begin
            return Const{T}(val1 - val2)
        end
        (BSImpl.Polyform(; poly = poly1), BSImpl.Polyform(; poly = poly2)) => begin
            return Polyform{T}(poly1 - poly2; type)
        end
        _ => return add_worker(T, (a, -b))
    end
end

-(a::Number, b::BasicSymbolic) = a + (-b)
-(a::BasicSymbolic, b::Number) = a + (-b)


mul_t(a,b) = promote_symtype(*, symtype(a), symtype(b))
mul_t(a) = promote_symtype(*, symtype(a))

*(a::BasicSymbolic) = a

function _mul_worker!(::Type{T}, num_coeff, den_coeff, num_dict, den_dict, term) where {T}
    if term isa BasicSymbolic{T}
        @match term begin
            BSImpl.Const(; val) => (num_coeff[] *= val)
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
    elseif term isa BasicSymbolic
        error("Cannot operate on symbolics with different vartypes. Found `$T` and `$(vartype(term))`.")
    else
        num_coeff[] *= term
    end
    return nothing
end

function coeff_dict_to_term(::Type{T}, type::TypeT, coeff, dict)::BasicSymbolic{T} where {T}
    @nospecialize type
    isempty(dict) && return Const{T}(coeff[])
    if isone(coeff[]) && length(dict) == 1
        k, v = first(dict)
        return (k ^ v)
    end
    pvars = PolyVarT[]
    partial_pvars = PolyVarT[]
    vars = ArgsT{T}()
    exps = Int[]
    sizehint!(pvars, length(dict))
    sizehint!(partial_pvars, length(dict))
    sizehint!(vars, length(dict))
    sizehint!(exps, length(dict))
    for (k, v) in dict
        if !isinteger(v)
            k = Term{T}(^, ArgsT{T}((k, v)); type)
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
    Polyform{T}(PolynomialT(coeff, mvec), partial_pvars, vars; type)
end

function mul_worker(::Type{T}, terms) where {T <: Union{SymReal, SafeReal}}
    length(terms) == 1 && return Const{T}(only(terms))
    a, bs = Iterators.peel(terms)
    a = unwrap(a)
    type::TypeT = symtype(a)
    for b in bs
        type = promote_symtype(*, type, symtype(b))
    end
    unsafes = ArgsT{T}()
    num_coeff = PolyCoeffT[1]
    den_coeff = PolyCoeffT[1]
    num_dict = Dict{BasicSymbolic{T}, Any}()
    den_dict = Dict{BasicSymbolic{T}, Any}()

    for term in terms
        term = unwrap_const(unwrap(term))
        if !issafecanon(*, term)
            push!(unsafes, Const{T}(term))
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
    num = coeff_dict_to_term(T, type, num_coeff, num_dict)
    den = coeff_dict_to_term(T, type, den_coeff, den_dict)
    if !isempty(unsafes)
        push!(unsafes, num)
        # ensure `num` is always the first
        unsafes[1], unsafes[end] = unsafes[end], unsafes[1]
        num = Term{T}(*, unsafes; type)
    end

    return Div{T}(num, den, false; type)
end

function *(a::T, b::T) where {T <: NonTreeSym}
    if !(symtype(a) <: Number) || !(symtype(b) <: Number)
        throw(MethodError(*, (a, b)))
    end
    mul_worker(vartype(T), (a, b))
end

function *(a::Number, b::NonTreeSym)
    if !(symtype(a) <: Number) || !(symtype(b) <: Number)
        throw(MethodError(*, (a, b)))
    end
    mul_worker(vartype(b), (a, b))
end

###
### Div
###

function /(a::Union{S,Number}, b::S) where {S <: NonTreeSym}
    if !(symtype(a) <: Number) || !(symtype(b) <: Number)
        throw(MethodError(/, (a, b)))
    end
    T = vartype(S)
    if isconst(a) || isconst(b)
        return Const{T}(unwrap_const(a) / unwrap_const(b))
    end
    type = promote_symtype(/, symtype(a), symtype(b))
    Div{T}(a, b, false; type)
end

*(a::NonTreeSym, b::Number) = b * a

\(a::T, b::Union{Number, T}) where {T <: NonTreeSym} = b / a

\(a::Number, b::NonTreeSym) = b / a

/(a::NonTreeSym, b::Number) = (isone(abs(b)) ? b : (b isa Integer ? 1//b : inv(b))) * a

//(a::Union{NonTreeSym, Number}, b::NonTreeSym) = a / b

//(a::NonTreeSym, b::Number) = (one(b) // b) * a


###
### Pow
###

function ^(a::BasicSymbolic{T}, b) where {T <: Union{SymReal, SafeReal}}
    if !(symtype(a) <: Number) || !(symtype(b) <: Number)
        throw(MethodError(^, (a, b)))
    end
    isconst(a) && return Const{T}(^(unwrap_const(a), b))
    a = unwrap_const(a)
    b = unwrap_const(unwrap(b))
    type = promote_symtype(^, symtype(a), symtype(b))
    !issafecanon(^, a, b) && return Term{T}(^, ArgsT{T}((a, Const{T}(b))); type)
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
    if b isa Number && isinteger(b)
        @match a begin
            BSImpl.Polyform(; poly, partial_polyvars, vars) && if polyform_variant(poly) != PolyformVariant.ADD end => begin
                poly = MP.polynomial(poly ^ Int(b), PolyCoeffT)
                return Polyform{T}(poly, copy(partial_polyvars), copy(vars); type)
            end
            _ => return Polyform{T}(MP.polynomial(basicsymbolic_to_polyvar(a) ^ Int(b), PolyCoeffT); type)
        end
    end
    return BSImpl.Term{T}(^, ArgsT{T}((a, Const{T}(b))); type)
end

function ^(a::Number, b::BasicSymbolic{T}) where {T}
    if !(symtype(a) <: Number) || !(symtype(b) <: Number)
        throw(MethodError(^, (a, b)))
    end
    type = promote_symtype(^, symtype(a), symtype(b))
    Term{T}(^, ArgsT{T}((Const{T}(a), b)); type)
end
