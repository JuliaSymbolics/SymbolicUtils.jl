Base.isequal(::BasicSymbolic, x::Union{Number, AbstractArray}) = false
Base.isequal(x::Union{Number, AbstractArray}, ::BasicSymbolic) = false
Base.isequal(::BasicSymbolic, ::Missing) = false
Base.isequal(::Missing, ::BasicSymbolic) = false

"""
Task-local flag to control whether equality comparisons include metadata and full type
information.
"""
const COMPARE_FULL = TaskLocalValue{Bool}(Returns(false))

"""
    $TYPEDSIGNATURES

Generated function which manually dispatches on `isequal` for common scalar types,
avoiding dynamic dispatch in common cases.
"""
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

"""
    $TYPEDSIGNATURES

Compare two dictionaries of the form inside `AddMul`. Handles the edge case where
the keys are hashed with `full=false` but the current comparison is with `full=true`.
`full` is a boolean which should be the current value of `COMPARE_FULL[]`. Passing it
allows avoiding repeatedly accessing a `TaskLocalValue`, which can be slow.
"""
function isequal_addmuldict(d1::ACDict{T}, d2::ACDict{T}, full::Bool) where {T}
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

"""
    $TYPEDSIGNATURES

Compare two dictionaries of the form of `ArrayOp.ranges`. Handles the edge case where
the keys are hashed with `full=false` but the current comparison is with `full=true`.
`full` is a boolean which should be the current value of `COMPARE_FULL[]`. Passing it
allows avoiding repeatedly accessing a `TaskLocalValue`, which can be slow.
"""
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

"""
    $TYPEDSIGNATURES

Core equality comparison for `BasicSymbolic`. `full` is the current value of
`COMPARE_FULL[]`, but passed explicitly to reduce accessing a `TaskLocalValue`.
"""
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
            isequal_somescalar(v1, v2)::Bool && (!full || (typeof(v1) === typeof(v2))::Bool)
        end
        (BSImpl.Sym(; name = n1, shape = s1, type = t1), BSImpl.Sym(; name = n2, shape = s2, type = t2)) => begin
            n1 === n2 && s1 == s2 && t1 === t2
        end
        (BSImpl.Term(; f = f1, args = args1, shape = s1, type = t1), BSImpl.Term(; f = f2, args = args2, shape = s2, type = t2)) => begin
            isequal(f1, f2) && isequal(args1, args2) && s1 == s2 && t1 === t2
        end
        (BSImpl.AddMul(; coeff = c1, dict = d1, variant = v1, shape = s1, type = t1), BSImpl.AddMul(; coeff = c2, dict = d2, variant = v2, shape = s2, type = t2)) => begin
            isequal_somescalar(c1, c2) && (!full || (typeof(c1) === typeof(c2))) && isequal_addmuldict(d1, d2, full) && isequal(v1, v2) && s1 == s2 && t1 === t2
        end
        (BSImpl.Div(; num = n1, den = d1, type = t1, shape = s1), BSImpl.Div(; num = n2, den = d2, type = t2, shape = s2)) => begin
            isequal_bsimpl(n1, n2, full) && isequal_bsimpl(d1, d2, full) && s1 == s2 && t1 === t2
        end
        (BSImpl.ArrayOp(; output_idx = o1, expr = e1, reduce = f1, term = t1, ranges = r1, shape = s1, type = type1), BSImpl.ArrayOp(; output_idx = o2, expr = e2, reduce = f2, term = t2, ranges = r2, shape = s2, type = type2)) => begin
            isequal(o1, o2) && isequal(e1, e2) && isequal(f1, f2)::Bool && isequal(t1, t2) && isequal_rangesdict(r1, r2, full) && s1 == s2 && type1 === type2
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

"""
    $TYPEDSIGNATURES

Manual dispatch on `hash` for common scalar types, avoiding dynamic dispatch when
`a` is uninferred.
"""
@inline @generated function hash_somescalar(a, h::UInt)
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

"""
    $TYPEDSIGNATURES

Hash `AddMul.dict`, accounting for the fact that the keys are inserted with `full=false`
when currently `full` may be `true`. `full` should be equal to the current value of
`COMPARE_FULL`. Passing `full` prevents repeatedly accessing a `TaskLocalValue`.
"""
function hash_addmuldict(d::ACDict, h::UInt, full::Bool)
    hv = Base.hasha_seed
    for (k, v) in d
        h1 = hash_somescalar(v, zero(UInt))
        h1 = hash_bsimpl(k, h1, full)
        hv ⊻= h1
    end
    return hash(hv, h)
end

"""
    $TYPEDSIGNATURES


Hash `ArrayOp.ranges`, accounting for the fact that the keys are inserted with `full=false`
when currently `full` may be `true`. `full` should be equal to the current value of
`COMPARE_FULL`. Passing `full` prevents repeatedly accessing a `TaskLocalValue`.
Compute a hash value for a ranges dictionary used in `ArrayOp` variants.
"""
function hash_rangesdict(d::RangesT, h::UInt, full::Bool)
    hv = Base.hasha_seed
    for (k, v) in d
        h1 = hash(v, zero(UInt))
        h1 = hash_bsimpl(k, h1, full)
        hv ⊻= h1
    end
    return hash(hv, h)
end

"""
    $METHODLIST

Custom hash functions for `vartype(x)`, since hashes of types defined in a module are not
stable across machines or processes.
"""
vartype_hash(::Type{SymReal}, h::UInt) = hash(0x3fffc14710d3391a, h)
vartype_hash(::Type{SafeReal}, h::UInt) = hash(0x0e8c1e3ac836f40d, h)
vartype_hash(::Type{TreeReal}, h::UInt) = hash(0x44ec30357ff75155, h)

"""
    $TYPEDSIGNATURES

Custom hash functions for `AddMul.variant`, since it falls back to the `Base.Enum`
implementation, which uses `objectid`, which changes across runs.
"""
hash_addmulvariant(x::AddMulVariant.T, h::UInt) = hash(x === AddMulVariant.ADD ? 0x6d86258fc9cc0742 : 0x5e0a17a14cd8c815, h)

const FNTYPE_SEED = 0x8b414291138f6c45

"""
    $TYPEDSIGNATURES

Custom hash function for a type that may be an `FnType`, since hashes of types defined in a module are not
stable across machines or processes.
"""
function hash_maybe_fntype(T::TypeT, h::UInt)
    @nospecialize T
    if T <: FnType
        hash(T.parameters[1], hash(T.parameters[2], hash(T.parameters[3], h)::UInt)::UInt)::UInt ⊻ FNTYPE_SEED
    else
        hash(T, h)::UInt
    end
end

"""
    hash_bsimpl(s::BSImpl.Type{T}, h::UInt, full) where {T}

Core hash function for `BasicSymbolic`. `full` must be equal to the current value of
`COMPARE_FULL[]`. Passing it reduces repeated access of a `TaskLocalValue`.
"""
function hash_bsimpl(s::BSImpl.Type{T}, h::UInt, full) where {T}
    if !iszero(h)
        return hash(hash_bsimpl(s, zero(h), full), h)::UInt
    end
    h = vartype_hash(T, h)

    partial::UInt = @match s begin
        BSImpl.Const(; val, hash) => begin
            if iszero(hash)
                h = s.hash = hash_somescalar(val, h)::UInt
            else
                h = hash
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
            h = hash_maybe_fntype(type, h)
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
            htmp = hash_somescalar(coeff, hash_addmuldict(dict, hash_addmulvariant(variant, Base.hash(shape, Base.hash(type, h))), full))
            if full
                htmp = Base.hash(typeof(coeff), htmp)
            end
            htmp
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

const ENABLE_HASHCONSING = Ref(true)
const WCS_LOCK = ReentrantLock()
const WCS_SYMREAL = WeakCacheSet{BasicSymbolic{SymReal}}()
const WCS_SAFEREAL = WeakCacheSet{BasicSymbolic{SafeReal}}()
const WCS_TREEREAL = WeakCacheSet{BasicSymbolic{TreeReal}}()

@inline wcs_for_vartype(::Type{SymReal}) = WCS_SYMREAL
@inline wcs_for_vartype(::Type{SafeReal}) = WCS_SAFEREAL
@inline wcs_for_vartype(::Type{TreeReal}) = WCS_TREEREAL

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

function hashcons(s::BSImpl.Type{T}, reregister = false) where {T}
    if !ENABLE_HASHCONSING[]
        return s
    end
    s.id === nothing || reregister || return s
    @manually_scope COMPARE_FULL => true begin
        k = (@lock WCS_LOCK getkey!(wcs_for_vartype(T), s))::typeof(s)
        if k.id === nothing
            k.id = generate_id()
        end
        return k::typeof(s)
    end true
end

const CONST_ZERO_SYMREAL = hashcons(BSImpl.Const{SymReal}(0, 0, nothing))
const CONST_ZERO_SAFEREAL = hashcons(BSImpl.Const{SafeReal}(0, 0, nothing))
const CONST_ZERO_TREEREAL = hashcons(BSImpl.Const{TreeReal}(0, 0, nothing))
const CONST_ONE_SYMREAL = hashcons(BSImpl.Const{SymReal}(1, 0, nothing))
const CONST_ONE_SAFEREAL = hashcons(BSImpl.Const{SafeReal}(1, 0, nothing))
const CONST_ONE_TREEREAL = hashcons(BSImpl.Const{TreeReal}(1, 0, nothing))

"""
    $TYPEDSIGNATURES

Get the default zero constant for a given `BasicSymbolic` variant type.

# Arguments
- Type parameter: `BasicSymbolic{SymReal}`, `BasicSymbolic{SafeReal}`, or `BasicSymbolic{TreeReal}`

# Returns
- A `Const` variant representing zero with the appropriate variant type
"""
@inline defaultval(::Type{BasicSymbolic{SymReal}}) =  CONST_ZERO_SYMREAL
@inline defaultval(::Type{BasicSymbolic{SafeReal}}) = CONST_ZERO_SAFEREAL
@inline defaultval(::Type{BasicSymbolic{TreeReal}}) = CONST_ZERO_TREEREAL

"""
    $(TYPEDSIGNATURES)

Return a `Const` representing `0` with the provided `vartype`.
"""
@inline zero_of_vartype(::Type{SymReal}) = CONST_ZERO_SYMREAL
@inline zero_of_vartype(::Type{SafeReal}) = CONST_ZERO_SAFEREAL
@inline zero_of_vartype(::Type{TreeReal}) = CONST_ZERO_TREEREAL
"""
    $(TYPEDSIGNATURES)

Return a `Const` representing `1` with the provided `vartype`.
"""
@inline one_of_vartype(::Type{SymReal}) = CONST_ONE_SYMREAL
@inline one_of_vartype(::Type{SafeReal}) = CONST_ONE_SAFEREAL
@inline one_of_vartype(::Type{TreeReal}) = CONST_ONE_TREEREAL

