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

@noinline function _throw_cartesian_indexing()
    throw(ArgumentError("Symbolic `getindex` requires cartesian indexing."))
end

function promote_symtype(::typeof(getindex), ::Type{T}, Ts...) where {N, eT, T <: AbstractArray{eT, N}}
    _throw_cartesian_indexing()
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
    is_array_shape(sharr) || isempty(shidxs) || throw_not_array(sharr)
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
    _getindex(SymReal, arr, idxs...)
end
@cache function _getindex_2(arr::BasicSymbolic{SafeReal}, idxs::Union{BasicSymbolic{SafeReal}, Int, AbstractRange{Int}, Colon}...)::BasicSymbolic{SafeReal}
    _getindex(SafeReal, arr, idxs...)
end

"""
    $TYPEDEF

A wrapper around a small vector of integer indices that provides a stable,
allocation-efficient representation of multi-dimensional array indices.

This type is used in conjunction with [`StableIndices`](@ref) to iterate over
multi-dimensional index spaces in a type-stable manner. It implements the
standard iteration and indexing interfaces.

This is effectively equivalent to `CartesianIndex` for symbolic arrays, but
avoids type-instability due to `N` in `CartesianIndex{N}` being uninferrable.

# Fields
$TYPEDFIELDS

# See also
- [`StableIndices`](@ref): An iterator that produces `StableIndex` values.
- [`stable_eachindex`](@ref): Returns a `StableIndices` iterator for a symbolic array.
"""
struct StableIndex{I}
    """
    A small vector storing the indices for each dimension. Indices can either be integers
    or `BasicSymbolic`s where all values have integer symtypes.
    """
    idxs::SmallV{I}

    StableIndex(idxs::SmallV{Int}) = new{Int}(idxs)
    function StableIndex(idxs::AbstractVector{Int})
        _idxs = SmallV{Int}()
        sizehint!(_idxs, length(idxs))
        append!(_idxs, idxs)
        return new{Int}(_idxs)
    end
    StableIndex(idxs::SmallV{BasicSymbolic{T}}) where {T} = new{BasicSymbolic{T}}(idxs)
    function StableIndex(idxs::AbstractVector{BasicSymbolic{T}}) where {T}
        _idxs = SmallV{BasicSymbolic{T}}()
        sizehint!(_idxs, length(idxs))
        for x in idxs
            @assert symtype(x) <: Integer
        end
        append!(_idxs, idxs)
        return new{BasicSymbolic{T}}(_idxs)
    end
end

"""
    $TYPEDSIGNATURES

Build a `StableIndex` from an indexed symbolic `sym`. Requires that all indices are
integers.
"""
function StableIndex{Int}(sym::BasicSymbolic{T}) where {T}
    idxs = SmallV{Int}()
    @match sym begin
        BSImpl.Term(; f, args) && if f === getindex end => begin
            sizehint!(idxs, length(args) - 1)
            for i in 2:length(args)
                push!(idxs, unwrap_const(args[i])::Int)
            end
            return StableIndex(idxs)
        end
        _ => throw(ArgumentError("Can only build `StableIndex{Int}` from indexed symbolic."))
    end
end

Base.getindex(x::StableIndex, i::Int) = x.idxs[i]
Base.length(x::StableIndex) = length(x.idxs)
Base.iterate(x::StableIndex, args...) = iterate(x.idxs, args...)
Base.eltype(::Type{StableIndex}) = Int
Base.isequal(a::StableIndex{T}, b::StableIndex{T}) where {T} = isequal(a.idxs, b.idxs)
const STABLE_INDEX_SEED = 0x47da907bc9126ce1
Base.hash(a::StableIndex, h::UInt) = hash(a.idxs, h) ⊻ STABLE_INDEX_SEED

function Base.to_indices(A, inds, I::Tuple{StableIndex{Int}})
    return (as_linear_idx(axes(A), I[1]),)
end

"""
    $TYPEDSIGNATURES

Turn the index `I` into a linear index into an array for which `Base.axes` returns `sh`.
"""
@generated function as_linear_idx(sh::NTuple{N}, I::StableIndex{Int}) where {N}
    return quote
        linear_idx = 1
        acc = 1
        Base.@nexprs $N i -> begin
            ax = sh[i]
            linear_idx += (I.idxs[i] - first(ax)) * acc
            acc *= length(ax)
        end
        return linear_idx
    end
end

"""
    $TYPEDSIGNATURES

Turn the index `I` into a linear index into an array of shape `sh`.
"""
function as_linear_idx(sh::ShapeVecT, sidxs::StableIndex)
    linear_idx = 1
    acc = 1
    for i in eachindex(sh)
        ax = sh[i]
        linear_idx += (sidxs.idxs[i] - first(ax)) * acc
        acc *= length(ax)
    end
    return linear_idx
end

# To act as a function barrier
function scalar_index(@nospecialize(val), idx::Int)
    vec(val)[idx]
end

function Base.getindex(arr::BasicSymbolic{SymReal}, idxs::StableIndex)
    _stable_getindex_1(arr, idxs)
end
function Base.getindex(arr::BasicSymbolic{SafeReal}, idxs::StableIndex)
    _stable_getindex_2(arr, idxs)
end

@cache function _stable_getindex_1(arr::BasicSymbolic{SymReal}, sidxs::StableIndex{Int})::BasicSymbolic{SymReal}
    __stable_getindex(arr, sidxs)
end
@cache function _stable_getindex_2(arr::BasicSymbolic{SafeReal}, sidxs::StableIndex{Int})::BasicSymbolic{SafeReal}
    __stable_getindex(arr, sidxs)
end
function _stable_getindex_1(arr::BasicSymbolic{SymReal}, sidxs::StableIndex)
    __stable_getindex(arr, sidxs)
end
function _stable_getindex_2(arr::BasicSymbolic{SafeReal}, sidxs::StableIndex)
    __stable_getindex(arr, sidxs)
end

function _throw_arraymaker_out_of_range(x::BasicSymbolic, idx)
    throw(ArgumentError("Index $idx is out of range for `$x`."))
end

function __stable_getindex(arr::BasicSymbolic{T}, sidxs::StableIndex{I}) where {T, I}
    idxs = sidxs.idxs
    isempty(idxs) && return arr
    sh = shape(arr)
    if I === Int
        sh = sh::ShapeVecT
        @match arr begin
            BSImpl.Const(; val) => return Const{T}(scalar_index(val, as_linear_idx(sh, sidxs)))
            BSImpl.Term(; f, args) && if f === array_literal end => begin
                return args[1 + as_linear_idx(sh, sidxs)]
            end
            BSImpl.Term(; f, args) && if f isa TypeT && f <: CartesianIndex end => begin
                return args[as_linear_idx(sh, sidxs)]
            end
            BSImpl.ArrayMaker(; regions, values) => begin
                length(sh) == length(idxs) || _throw_cartesian_indexing()
                @union_split_smallvec regions @union_split_smallvec values @union_split_smallvec idxs begin
                    for (reg, val) in Iterators.reverse(zip(regions, values))
                        @union_split_smallvec reg begin
                            all(splat(in), zip(idxs, reg)) || continue
                            new_idxs = SmallV{Int}()
                            sizehint!(new_idxs, length(idxs))
                            for (idx, ax) in zip(idxs, reg)
                                push!(new_idxs, idx - first(ax) + 1)
                            end
                            return __stable_getindex(val, StableIndex(new_idxs))
                        end
                    end
                    _throw_arraymaker_out_of_range(arr, sidxs)
                end
            end
            _ => nothing
        end
    end
    @match arr begin
        BSImpl.Term(; f, args) && if f isa Operator && length(args) == 1 end => begin
            inner = args[1][sidxs]
            return BSImpl.Term{T}(f, ArgsT{T}((inner,)); type = symtype(inner), shape = ShapeVecT())
        end
        BSImpl.Term(; f, args) && if f === getindex && all(isconst, Iterators.drop(args, 1)) && !any(x -> x isa BasicSymbolic{T}, idxs) end => begin
            newargs = ArgsT{T}()
            push!(newargs, args[1])
            type = eltype(symtype(arr))::TypeT
            newshape = ShapeVecT()
            idxs_i = 1
            for oldidx in Iterators.drop(args, 1)
                oldidx_sh = shape(oldidx)
                if !is_array_shape(oldidx_sh)
                    push!(newargs, oldidx)
                    continue
                end
                idx = idxs[idxs_i]
                idxs_i += 1
                # special case when `oldidx` is `Colon()`
                if length(oldidx_sh) == 1 && oldidx_sh[1] == 1:0
                    push!(newargs, Const{T}(idx))
                else
                    push!(newargs, Const{T}(unwrap_const(oldidx)[idx]))
                end
            end
            @assert idxs_i == length(idxs) + 1
            return BSImpl.Term{T}(f, newargs; type, shape = newshape)
        end
        _ => nothing
    end
    type = eltype(symtype(arr))::TypeT
    newshape = ShapeVecT()
    @match arr begin
        BSImpl.ArrayOp(; output_idx, expr, ranges, reduce, term) => begin
            subrules = Dict{BasicSymbolic{T}, Union{BasicSymbolic{T}, Int}}()
            empty!(subrules)
            idxsym_idx = 1
            idxsym = idxs_for_arrayop(T)
            for (i, (newidx, outidx)) in enumerate(zip(idxs, output_idx))
                if outidx isa BasicSymbolic{T}
                    if haskey(ranges, outidx)
                        subrules[outidx] = ranges[outidx][newidx]
                    else
                        subrules[outidx] = newidx
                    end
                end
            end
            new_expr = reduce_eliminated_idxs(expr, output_idx, ranges, reduce)
            result = substitute(new_expr, subrules; fold = Val{false}(), filterer = !isarrayop)
            return result
        end
        _ => begin
            args = ArgsT{T}((arr,))
            for i in idxs
                push!(args, Const{T}(i))
            end
            return BSImpl.Term{T}(getindex, args; type, shape = newshape)
        end
    end
end

Base.@propagate_inbounds function _getindex(::Type{T}, arr::BasicSymbolic{T}, idxs::Union{BasicSymbolic{T}, Int, AbstractRange{Int}, Colon}...) where {T}
    @match arr begin
        BSImpl.Const(; val) && if all(x -> !(x isa BasicSymbolic{T}) || isconst(x), idxs) end => return Const{T}(val[unwrap_const.(idxs)...])
        BSImpl.Term(; f) && if f === array_literal && all(x -> !(x isa BasicSymbolic{T}) || isconst(x), idxs) end => begin
            return Const{T}(reshape(@view(arguments(arr)[2:end]), Tuple(size(arr)))[unwrap_const.(idxs)...])
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
            idxs_i = 1
            for oldidx in Iterators.drop(args, 1)
                oldidx_sh = shape(oldidx)
                if !is_array_shape(oldidx_sh)
                    push!(newargs, oldidx)
                    continue
                end
                idx = idxs[idxs_i]
                idxs_i += 1
                # special case when `oldidx` is `Colon()`
                if length(oldidx_sh) == 1 && oldidx_sh[1] == 1:0
                    push!(newargs, Const{T}(idx))
                elseif idx isa Colon
                    push!(newargs, oldidx)
                else
                    push!(newargs, Const{T}(unwrap_const(oldidx)[idx]))
                end
            end
            @assert idxs_i == length(idxs) + 1
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
                            _newidx = unwrap_const(newidx)::Union{BasicSymbolic{T}, Int}
                            subrules[outidx] = if _newidx isa Int
                                ranges[outidx][_newidx]
                            else
                                BSImpl.Const{T}(ranges[outidx])[_newidx]
                            end
                        else
                            subrules[outidx] = unwrap_const(newidx)::Union{BasicSymbolic{T}, Int}
                        end
                    end
                end
            end
            if isempty(new_output_idx)
                new_expr = reduce_eliminated_idxs(expr, output_idx, ranges, reduce)
                result = substitute(new_expr, subrules; fold = Val{false}(), filterer = !isarrayop)
                return result
            else
                new_expr = substitute(expr, subrules; fold = Val{false}(), filterer = !isarrayop)
                if term !== nothing
                    term = getindex(term, idxs...)
                end
                return BSImpl.ArrayOp{T}(new_output_idx, new_expr, reduce, term, new_ranges; type, shape = newshape)
            end
        end
        BSImpl.ArrayMaker(;) && if all(Base.Fix2(isa, Int), idxs) end => begin
            return getindex(arr, StableIndex(SmallV{Int}(idxs)))
        end
        _ => begin
            if is_array_shape(newshape)
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
            elseif is_array_shape(sh)
                return BSImpl.Term{T}(getindex, ArgsT{T}((arr, Const{T}.(idxs)...)); type, shape = newshape)
            else
                return arr
            end
        end
    end
end
function _getindex(::Type{T}, x::AbstractArray, idxs...) where {T}
    Const{T}(getindex(x, idxs...))
end
Base.getindex(x::BasicSymbolic{T}, i::CartesianIndex) where {T} = x[Tuple(i)...]
