"""
    $TYPEDSIGNATURES

Convert various metadata inputs into standardized `ImmutableDict` format.

# Arguments
- `x`: Metadata input (can be `MetadataT`, `Nothing`, or an iterable of key-value pairs)

# Returns
- `Nothing` if input is `Nothing`
- The input unchanged if already in `MetadataT` format
- A new `ImmutableDict{DataType, Any}` constructed from the key-value pairs otherwise
"""
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

"""
    $TYPEDSIGNATURES

Convert argument tuples or vectors into standardized `ArgsT` format for a variant type.

# Arguments
- `T`: The `SymVariant` type (`SymReal`, `SafeReal`, or `TreeReal`)
- `args`: Tuple or vector of arguments to convert

# Returns
- An `ArgsT{T}` containing the arguments, with non-`BasicSymbolic` values wrapped in `Const{T}`

# Details
This function normalizes arguments for symbolic operations. If arguments are already in
`ArgsT{T}` format, returns them unchanged. For `ROArgsT{T}`, extracts the parent. Otherwise,
creates a new `ArgsT{T}` and wraps each non-symbolic argument in a `Const{T}` variant. This
ensures all arguments to symbolic operations are properly typed `BasicSymbolic` objects.
"""
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

"""
    $TYPEDSIGNATURES

Unwrap arguments if any need unwrapping, otherwise return them unchanged.

# Arguments
- `args`: Arguments to potentially unwrap (can be `ArgsT`, `ROArgsT`, or other collections)

# Returns
- The original `args` if already in `ArgsT` or `ROArgsT` format
- The original `args` if no element needs unwrapping
- A new collection with all elements unwrapped otherwise

# Details
This function optimizes argument unwrapping by checking first if any element needs unwrapping.
If none do, it returns the original collection to avoid unnecessary allocations. For `ArgsT`
and `ROArgsT` types, which are already in normalized form, always returns the input unchanged.
Used in constructor functions to ensure arguments are in their simplest form.
"""
function unwrap_args(args)
    if any(x -> unwrap(x) !== x, args)
        map(unwrap, args)
    else
        args
    end
end
unwrap_args(args::ArgsT) = args
unwrap_args(args::ROArgsT) = args

"""
    $TYPEDSIGNATURES

Convert a dictionary into standardized `ACDict{T}` format for `AddMul`.

# Arguments
- `::Type{T}`: The `SymVariant` type (`SymReal`, `SafeReal`, or `TreeReal`)
- `dict::AbstractDict`: Dictionary to convert

# Returns
- The input if already in `ACDict{T}` format
- A new `ACDict{T}` populated with all key-value pairs otherwise
"""
function parse_dict(::Type{T}, dict::AbstractDict) where {T}
    dict isa ACDict{T} && return dict
    _dict = ACDict{T}()
    for (k, v) in dict
        _dict[k] = v
    end
    return _dict::ACDict{T}
end

"""
    $TYPEDSIGNATURES

Unwrap dictionary keys if any need unwrapping, preserving values unchanged.

# Arguments
- `dict`: A dictionary whose keys might need unwrapping

# Returns
- The original dictionary if no key needs unwrapping
- A new dictionary of the same type with unwrapped keys otherwise

# Details
This function optimizes dictionary key unwrapping by checking first if any key needs
unwrapping. If none do, returns the original dictionary to avoid allocations. Otherwise,
creates a new dictionary of the same type with all keys unwrapped but values preserved.
Used to normalize dictionaries used in symbolic expressions where keys might be wrapped
symbolic values.
"""
function unwrap_dict(dict)
    if any(x -> unwrap(x) !== x, keys(dict))
        typeof(dict)(unwrap(k) => v for (k, v) in dict)
    else
        dict
    end
end

"""
    $TYPEDSIGNATURES

Convert output indices into standardized `OutIdxT{T}` format for `ArrayOp` variants.

# Arguments
- `::Type{T}`: The `SymVariant` type (`SymReal`, `SafeReal`, or `TreeReal`)
- `outidxs`: Tuple or vector of output indices

# Returns
- The input if already in `OutIdxT{T}` format
- A new `OutIdxT{T}` with all indices unwrapped to their constant values otherwise
"""
function parse_output_idxs(::Type{T}, outidxs::Union{Tuple, AbstractVector}) where {T}
    outidxs isa OutIdxT{T} && return outidxs
    _outidxs = OutIdxT{T}()
    sizehint!(_outidxs, length(outidxs))
    for i in outidxs
        push!(_outidxs, unwrap_const(unwrap(i)))
    end
    return _outidxs::OutIdxT{T}
end

"""
    $TYPEDSIGNATURES

Normalize shape inputs into either `Unknown` or `ShapeVecT` format.

# Arguments
- `sh`: Shape input (can be `Unknown`, `ShapeVecT`, or an iterable of ranges)

# Returns
- The input if already `Unknown` or `ShapeVecT`
- A new `ShapeVecT` constructed from the iterable otherwise
"""
function parse_shape(sh)
    sh isa Unknown && return sh
    sh isa ShapeVecT && return sh
    _sh = ShapeVecT()
    for dim in sh
        push!(_sh, dim)
    end
    return _sh
end

"""
    $TYPEDSIGNATURES

Convert a dictionary of ranges into standardized `RangesT{T}` format for `ArrayOp`.

# Arguments
- `::Type{T}`: The `SymVariant` type (`SymReal`, `SafeReal`, or `TreeReal`)
- `dict::AbstractDict`: Dictionary mapping index variables to ranges

# Returns
- The input if already in `RangesT{T}` format
- A new `RangesT{T}` with all keys and values unwrapped otherwise
"""
function parse_rangedict(::Type{T}, dict::AbstractDict) where {T}
    dict isa RangesT{T} && return dict
    _dict = RangesT{T}()
    for (k, v) in dict
        _dict[unwrap_const(unwrap(k))] = unwrap_const(unwrap(v))
    end
    return _dict::RangesT{T}
end

"""
    $TYPEDSIGNATURES

Check if an object is or contains symbolic expressions.

# Arguments
- `O`: Any object to check

# Returns
- `Bool`: `true` if `O` is a symbolic, code primitive, array of symbolics, or tuple of symbolics
"""
function _is_tuple_or_array_of_symbolics(O)
    return O isa Code.CodegenPrimitive ||
        (symbolic_type(O) != NotSymbolic() && !(O isa Union{Symbol, Expr})) ||
        _is_array_of_symbolics(O) ||
        _is_tuple_of_symbolics(O)
end

"""
    $TYPEDSIGNATURES

Check if an object is a non-symbolic array containing symbolic elements.
"""
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

"""
    $TYPEDSIGNATURES

Check if a tuple contains symbolic elements.
"""
function _is_tuple_of_symbolics(O::Tuple)
    return any(_is_tuple_or_array_of_symbolics, O)
end
_is_tuple_of_symbolics(O) = false

"""
    $TYPEDSIGNATURES

Utility function used as the operation of expressions representing an array of symbolic values.
See [`SymbolicUtils.BSImpl.Const`](@ref) for more details.

The first argument `sz` is the `size` of the represented array. `args...` is `prod(sz)`
elements representing the elements of the array in column-major order.
"""
array_literal(sz::NTuple{N, Int}, args...) where {N} = reshape(Base.vect(args...), sz)

"""
    BSImpl.Const{T}(val) where {T}

Constructor for a symbolic expression that wraps a constant value `val`. Also converts
arrays/tuples of symbolics to symbolic expressions.

# Arguments
- `val`: The value to wrap (can be any type including arrays and tuples)

# Returns
- `BasicSymbolic{T}`: A `Const` variant or specialized representation

# Details
This is the low-level constructor for constant expressions. It handles several special cases:
1. If `val` is already a `BasicSymbolic{T}`, returns it unchanged
2. If `val` is a `BasicSymbolic` of a different variant type, throws an error
3. If `val` is an array containing symbolic elements, creates a `Term` with
   [`SymbolicUtils.array_literal`](@ref) operation
4. If `val` is a tuple containing symbolic elements, creates a `Term` with `tuple` operation
5. Otherwise, creates a `Const` variant wrapping the value

# Extended help

The `unsafe` flag skips hash consing for performance in internal operations.
"""
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
        isadjoint = val isa LinearAlgebra.Adjoint
        istranspose = val isa LinearAlgebra.Transpose
        if isadjoint || istranspose
            val = parent(val)
        end
        args = ArgsT{T}((BSImpl.Const{T}(size(val); unsafe),))
        sizehint!(args, length(val) + 1)
        type = Union{}
        for v in val
            push!(args, BSImpl.Const{T}(v))
            type = promote_type(type, symtype(v))
        end
        shape = ShapeVecT(axes(val))
        type = Array{type, ndims(val)}
        term = BSImpl.Term{T}(array_literal, args; type, shape, unsafe)
        if isadjoint
            type = promote_symtype(adjoint, type)
            shape = promote_shape(adjoint, shape)
            term = BSImpl.Term{T}(adjoint, ArgsT{T}((term,)); type, shape, unsafe)
        elseif istranspose
            type = promote_symtype(transpose, type)
            shape = promote_shape(transpose, shape)
            term = BSImpl.Term{T}(transpose, ArgsT{T}((term,)); type, shape, unsafe)
        end
        return term
    elseif val isa Tuple && _is_tuple_of_symbolics(val)
        args = ArgsT{T}()
        sizehint!(args, length(val))
        for v in val
            push!(args, BSImpl.Const{T}(v))
        end
        types = symtype.(val)
        type = Tuple{types...}
        shape = ShapeVecT((1:length(val),))
        return BSImpl.Term{T}(tuple, args; type, shape, unsafe)
    else
        props = ordered_override_properties(BSImpl.Const)
        var = BSImpl.Const{T}(val, props...)
        if !unsafe
            var = hashcons(var)
        end
        return var
    end
end

"""
    BSImpl.Sym{T}(name::Symbol; metadata = nothing, type, shape = default_shape(type)) where {T}

Internal constructor for symbolic variables.

# Arguments
- `name::Symbol`: The name of the symbolic variable
- `metadata`: Optional metadata dictionary (default: `nothing`)
- `type`: The symbolic type of the variable (required keyword argument)
- `shape`: The shape of the variable (default: inferred from `type`)

# Returns
- `BasicSymbolic{T}`: A `Sym` variant representing the symbolic variable

# Details
This is the low-level constructor for symbolic variables. It normalizes the metadata
and shape inputs, populates default properties using `ordered_override_properties`,
and performs hash consing. The `type` parameter determines the Julia type
that this symbolic variable represents.

# Extended help

The `unsafe` keyword argument (default: `false`) can be used to skip hash consing for
performance in internal operations.
"""
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

"""
    BSImpl.Term{T}(f, args; metadata = nothing, type, shape = default_shape(type)) where {T}

Internal constructor for function application terms.

# Arguments
- `f`: The function or operation to apply
- `args`: The arguments to the function (normalized to `ArgsT{T}`)
- `metadata`: Optional metadata dictionary (default: `nothing`)
- `type`: The result type of the function application (required keyword argument)
- `shape`: The shape of the result (default: inferred from `type`)

# Returns
- `BasicSymbolic{T}`: A `Term` variant representing the function application

# Details
This is the low-level constructor for function application expressions. It represents
`f(args...)` symbolically. The constructor normalizes metadata, shape, and arguments,
populates default properties, and performs hash consing. The `type` parameter
should be the expected return type of calling `f` with `args`.

# Extended help

The `unsafe` keyword argument (default: `false`) can be used to skip hash consing for
performance in internal operations.
"""
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

"""
    BSImpl.AddMul{T}(coeff, dict, variant::AddMulVariant.T; metadata = nothing, type, shape = default_shape(type)) where {T}

Internal constructor for addition and multiplication expressions.

# Arguments
- `coeff`: The leading coefficient (for addition) or coefficient (for multiplication)
- `dict`: Dictionary mapping terms to their coefficients/exponents (normalized to `ACDict{T}`)
- `variant::AddMulVariant.T`: Either `AddMulVariant.ADD` or `AddMulVariant.MUL`
- `metadata`: Optional metadata dictionary (default: `nothing`)
- `type`: The result type of the operation (required keyword argument)
- `shape`: The shape of the result (default: inferred from `type`)

# Returns
- `BasicSymbolic{T}`: An `AddMul` variant representing the sum or product

# Details
This is the low-level constructor for optimized addition and multiplication expressions.
For addition, represents `coeff + sum(k * v for (k, v) in dict)`. For multiplication,
represents `coeff * prod(k ^ v for (k, v) in dict)`. The constructor normalizes all
inputs and performs hash consing.

# Extended help

The `unsafe` keyword argument (default: `false`) can be used to skip hash consing for
performance in internal operations.
"""
@inline function BSImpl.AddMul{T}(coeff, dict, variant::AddMulVariant.T; metadata = nothing, type, shape = default_shape(type), unsafe = false) where {T}
    @nospecialize coeff
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

"""
    BSImpl.Div{T}(num, den, simplified::Bool; metadata = nothing, type, shape = default_shape(type)) where {T}

Internal constructor for division expressions.

# Arguments
- `num`: The numerator (converted to `Const{T}`)
- `den`: The denominator (converted to `Const{T}`)
- `simplified::Bool`: Whether the division has been simplified
- `metadata`: Optional metadata dictionary (default: `nothing`)
- `type`: The result type of the division (required keyword argument)
- `shape`: The shape of the result (default: inferred from `type`)

# Returns
- `BasicSymbolic{T}`: A `Div` variant representing the division

# Details
This is the low-level constructor for division expressions. It represents `num / den`
symbolically. Both numerator and denominator are automatically wrapped in `Const{T}`
if not already symbolic. The `simplified` flag tracks whether simplification has been
attempted. The constructor normalizes all inputs and performs hash consing.

# Extended help

The `unsafe` keyword argument (default: `false`) can be used to skip hash consing for
performance in internal operations.
"""
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

"""
    BSImpl.ArrayOp{T}(output_idx, expr::BasicSymbolic{T}, reduce, term, ranges = default_ranges(T); metadata = nothing, type, shape = default_shape(type)) where {T}

Internal constructor for array operation expressions.

# Arguments
- `output_idx`: Output indices defining the result array dimensions (normalized to `OutIdxT{T}`)
- `expr::BasicSymbolic{T}`: The expression to evaluate for each index combination
- `reduce`: Reduction operation to apply (or `nothing` for direct assignment)
- `term`: Optional term for accumulation (or `nothing`)
- `ranges`: Dictionary mapping index variables to their ranges (default: empty)
- `metadata`: Optional metadata dictionary (default: `nothing`)
- `type`: The result type (required keyword argument, typically an array type)
- `shape`: The shape of the result (default: inferred from `type`)

# Returns
- `BasicSymbolic{T}`: An `ArrayOp` variant representing the array operation

# Details
This is the low-level constructor for array comprehension-like operations. It represents
operations like `[expr for i in range1, j in range2]` with optional reduction. The
constructor normalizes all inputs, unwraps constants where appropriate, and optionally
performs hash consing.

The [`ArrayOp`](@ref) constructor should be strongly preferred.

# Extended help

The `unsafe` keyword argument (default: `false`) can be used to skip hash consing for
performance in internal operations.
"""
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

