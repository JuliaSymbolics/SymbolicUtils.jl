struct Const{T} end
struct Sym{T} end
struct Term{T} end
struct Add{T} end
struct Mul{T} end
struct Div{T} end
struct ArrayOp{T} end

"""
    Const{T}(val) where {T}

Alias for [`BSImpl.Const{T}`](@ref).
"""
@inline Const{T}(@nospecialize(val); unsafe = false) where {T} = BSImpl.Const{T}(val; unsafe)

"""
    Sym{T}(name; kw...) where {T}

Alias for [`BSImpl.Sym{T}`](@ref).
"""
@inline Sym{T}(name; kw...) where {T} = BSImpl.Sym{T}(name; kw...)

"""
    Term{T}(f, args; type = _promote_symtype(f, args), kw...) where {T}

Alias for [`BSImpl.Term{T}`](@ref) except it also unwraps `args`.
"""
@inline function Term{T}(f, args; type = _promote_symtype(f, args), kw...) where {T}
    args = unwrap_args(args)
    BSImpl.Term{T}(f, args; type, kw...)
end

"""
    Add{T}(coeff, dict; kw...) where {T}

High-level constructor for addition expressions.

# Arguments
- `coeff`: The constant term (additive offset)
- `dict`: Dictionary mapping terms to their coefficients
- `kw...`: Additional keyword arguments (e.g., `type`, `shape`, `metadata`, `unsafe`)

# Returns
- `BasicSymbolic{T}`: An optimized representation of `coeff + sum(k * v for (k, v) in dict)`

# Details

This constructor maintains invariants required by the `AddMul` variant. This should be
preferred over the `BSImpl.AddMul{T}` constructor.
"""
@inline function Add{T}(coeff, dict; kw...) where {T}
    @nospecialize coeff kw
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

"""
    Mul{T}(coeff, dict; kw...) where {T}

High-level constructor for multiplication expressions.

# Arguments
- `coeff`: The multiplicative coefficient
- `dict`: Dictionary mapping base terms to their exponents
- `kw...`: Additional keyword arguments (e.g., `type`, `shape`, `metadata`, `unsafe`)

# Returns
- `BasicSymbolic{T}`: An optimized representation of `coeff * prod(k ^ v for (k, v) in dict)`

# Details

This constructor maintains invariants required by the `AddMul` variant. This should be
preferred over the `BSImpl.AddMul{T}` constructor.
"""
@inline function Mul{T}(coeff, dict; kw...) where {T}
    @nospecialize coeff kw
    coeff = unwrap(coeff)
    dict = unwrap_dict(dict)
    if isempty(dict)
        return Const{T}(coeff)
    elseif _iszero(coeff)
        return zero_of_vartype(T)
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
                BSImpl.AddMul(; coeff = c2, dict = d2, variant) && if variant === AddMulVariant.ADD end => begin
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
    elseif safe_isinteger(x)
        (true, Int(x))
    elseif x isa Rat
        (true, x)
    else
        (false, NaN)
    end
end

"""
    safe_div(a::Number, b::Number)::Number

Perform division with automatic rational conversion for integer inputs.

# Arguments
- `a::Number`: The numerator
- `b::Number`: The denominator

# Returns
- `Number`: The result of `a / b`, using rational arithmetic for integers
"""
function safe_div(a::Number, b::Number)::Number
    # @nospecialize a b
    if (!(a isa Integer) && safe_isinteger(a))
        a = Int(a)
    end
    if (!(b isa Integer) && safe_isinteger(b))
        b = Int(b)
    end
    if a isa Integer && b isa Integer
        return a // b
    end
    return a / b
end

"""
    Div{T}(n, d, simplified; type = promote_symtype(/, symtype(n), symtype(d)), kw...) where {T}

High-level constructor for division expressions with simplification.

# Arguments
- `n`: The numerator
- `d`: The denominator
- `simplified::Bool`: Whether simplification has been attempted
- `type`: The result type (default: inferred using `promote_symtype`)
- `kw...`: Additional keyword arguments (e.g., `shape`, `metadata`, `unsafe`)

# Returns
- `BasicSymbolic{T}`: An optimized representation of `n / d`

# Details
This constructor creates symbolic division expressions with extensive simplification:
- Zero numerator returns zero
- Unit denominator returns the numerator
- Zero denominator returns `Const{T}(1 // 0)` (infinity). Any infinity may be returned.
- Nested divisions are flattened
- Constant divisions are evaluated
- Rational coefficients are simplified
- Multiplications in numerator/denominator are handled specially

For non-`SafeReal` variants, automatic cancellation is attempted using `quick_cancel`.
The `simplified` flag prevents infinite simplification loops.

"""
function Div{T}(n, d, simplified; type = promote_symtype(/, symtype(n), symtype(d)), kw...) where {T}
    n = Const{T}(unwrap(n))
    d = Const{T}(unwrap(d))

    if !(type <: Number)
        _iszero(n) && return Const{T}(n)
        _isone(d) && return Const{T}(n)
        return BSImpl.Div{T}(n, d, simplified; type, kw...)
    end

    if !(T === SafeReal)
        n, d = quick_cancel(Const{T}(n), Const{T}(d))
    end

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

    isconst(d) && _isone(-d) && return Const{T}(-n)
    if isconst(n) && isconst(d)
        nn = unwrap_const(n)
        dd = unwrap_const(d)
        nn isa Rat && dd isa Rat && return Const{T}(nn // dd)
        return Const{T}(nn / dd)
    end

    @match (n, d) begin
        (BSImpl.Const(; val = v1), BSImpl.Const(; val = v2)) => Const{T}(safe_div(v1, v2))
        (BSImpl.Const(; val = c1), BSImpl.AddMul(; coeff = c2, dict, type, shape, variant)) && if variant == AddMulVariant.MUL end => begin
            if c1 isa Rat && c2 isa Rat
                tmp = c1 // c2
                c1 = tmp.num
                c2 = tmp.den
            end
            n = Const{T}(c1)
            d = Mul{T}(c2, dict, ; type, shape)
        end
        (BSImpl.AddMul(; coeff, dict, type, shape, variant), BSImpl.Const(; val)) && if variant == AddMulVariant.MUL end => begin
            return Mul{T}(safe_div(coeff, val), dict, ; type, shape)
        end
        (BSImpl.AddMul(; coeff = c1, dict = d1, type = t1, shape = sh1, variant = v1),
            BSImpl.AddMul(; coeff = c2, dict = d2, type = t2, shape = sh2, variant = v2)) &&
            if v1 == AddMulVariant.MUL && v2 == AddMulVariant.MUL end => begin

            if c1 isa Rat && c2 isa Rat
                tmp = c1 // c2
                c1 = tmp.num
                c2 = tmp.den
            end
            n = Mul{T}(c1, d1, ; type = t1, shape = sh1)
            d = Mul{T}(c2, d2, ; type = t2, shape = sh2)
        end
        _ => nothing
    end

    _isone(d) && return Const{T}(n)
    _isone(-d) && return Const{T}(-n)

    BSImpl.Div{T}(n, d, simplified; type, kw...)
end

"""
    IndexedAxis{T}

Helper struct tracking how an array is indexed along one dimension.

# Fields
- `sym::BasicSymbolic{T}`: The array being indexed
- `dim::Int`: Which dimension of the array
- `pad::Union{Int, Nothing}`: Offset added to the index variable, or `nothing` for complex indexing

# Details
Used internally by `arrayop_shape` to track and validate index variable usage patterns.
"""
struct IndexedAxis{T}
    sym::BasicSymbolic{T}
    dim::Int
    pad::Union{Int, Nothing}
end

const IdxToAxesT{T} = Dict{BasicSymbolic{T}, Vector{IndexedAxis{T}}}

"""
    IndexedAxes{T}

Helper struct for tracking index variable usage in array operations.

# Fields
- `idx_to_axes::IdxToAxesT{T}`: Maps index variables to the axes they index
- `search_buffer::Set{BasicSymbolic{T}}`: Reusable buffer for variable searches
- `buffers::Vector{Vector{IndexedAxis{T}}}`: Pool of reusable buffers

# Details
Used internally for shape inference in `ArrayOp` expressions. Tracks which arrays
are indexed by which index variables and validates consistency.
"""
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

"""
    Base.setindex!(ix::IndexedAxes{T}, val::IndexedAxis{T}, ax::BasicSymbolic{T}) where {T}

Record that an index variable `ax` is used to index an array.

# Arguments
- `ix::IndexedAxes{T}`: The tracking structure
- `val::IndexedAxis{T}`: Information about how the array is indexed
- `ax::BasicSymbolic{T}`: The index variable
"""
function Base.setindex!(ix::IndexedAxes{T}, val::IndexedAxis{T}, ax::BasicSymbolic{T}) where {T}
    buffer = get!(() -> getbuffer(ix), ix.idx_to_axes, ax)
    push!(buffer, val)
    return ix
end

const INDEXED_AXES_BUFFER_SYMREAL = TaskLocalValue{IndexedAxes{SymReal}}(IndexedAxes{SymReal})
const INDEXED_AXES_BUFFER_SAFEREAL = TaskLocalValue{IndexedAxes{SafeReal}}(IndexedAxes{SafeReal})

"""
    _is_index_variable(expr::BasicSymbolic{T}) where T

Check if an expression is an index variable for array operations.

# Arguments
- `expr::BasicSymbolic{T}`: Expression to check
"""
function _is_index_variable end

for T in [SymReal, SafeReal, TreeReal]
    @eval function _is_index_variable(expr::BasicSymbolic{$T})
        iscall(expr) && operation(expr) === getindex && first(arguments(expr)) === idxs_for_arrayop($T)
    end
end

"""
    $TYPEDSIGNATURES

Extract and record index variable usage patterns from an expression.

# Arguments
- `ix::IndexedAxes{T}`: The tracking structure to populate
- `expr::BasicSymbolic{T}`: The expression to analyze

# Returns
- `IndexedAxes{T}`: The updated tracking structure

# Details
Recursively searches for `getindex` operations in the expression and records how
index variables are used. For each indexed array access, it identifies:
- Which array is being indexed
- Which dimension is accessed
- The offset applied to the index variable (if constant)

Special cases are optimized for performance:
- Direct index variables (`arr[i]`)
- Simple offsets (`arr[i + c]`)

For complex indexing patterns, searches for all index variables in the expression
and validates that only one is used per dimension.
"""
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
            BSImpl.AddMul(; variant, coeff, dict) && if variant == AddMulVariant.ADD && length(dict) == 1 && !iscall(first(keys(dict))) && _isone(first(values(dict))) end => begin
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

"""
    $TYPEDSIGNATURES

Wraps [`get_indexed_axes!`](@ref).
"""
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

"""
    $TYPEDSIGNATURES

Infer the shape of an `ArrayOp` result from index variables and ranges.

# Arguments
- `output_idx::AbstractVector`: Output index variables defining result dimensions
- `expr::BasicSymbolic{T}`: The expression being computed over indices
- `ranges::AbstractDict`: Dictionary mapping bound index variables to their ranges

# Returns
- `ShapeVecT`: The inferred shape of the result array
- `Unknown(length(output_idx))`: If shape cannot be fully inferred

# Throws
- `ArgumentError`: If index variable usage is inconsistent or out of bounds

# Details
This function performs comprehensive shape inference and validation:
1. Extracts all index variable usages from `expr`
2. For each bound index variable (in `ranges`), validates that its range fits within
   all arrays it indexes
3. For each unbound index variable, validates that all usages have consistent ranges
4. Constructs the output shape from the ranges of output index variables

The function ensures that array operations are well-formed before code generation.
"""
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

function promote_symtype(::Type{ArrayOp{T}}, _outidx::TypeT, expr::TypeT, _reduce::TypeT,
                         _term::TypeT, _ranges::TypeT) where {T}
    Array{expr}
end

"""
    ArrayOp{T}(output_idx, expr, reduce, term, ranges; metadata = nothing) where {T}

High-level constructor for array operation expressions.

# Arguments
- `output_idx`: Output indices defining result dimensions
- `expr`: Expression to evaluate for each index combination
- `reduce`: Reduction operation (or `nothing`)
- `term`: Optional accumulation term (or `nothing`)
- `ranges`: Dictionary mapping index variables to ranges
- `metadata`: Optional metadata (default: `nothing`)

# Returns
- `BasicSymbolic{T}`: An `ArrayOp` representing the array comprehension

# Details

This constructor validates and parses fields of the `ArrayOp` variant. It is usually never
called directly. Prefer using the [`@arrayop`](@ref) macro.

# Extended help

The `unsafe` keyword argument (default: `false`) can be used to skip hash consing for
performance in internal operations.
"""
function ArrayOp{T}(output_idx, expr, reduce, term, ranges; metadata = nothing, unsafe = false) where {T}
    if isempty(output_idx)
        type = symtype(expr)
    else
        type = Array{symtype(expr), length(output_idx)}
    end
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

