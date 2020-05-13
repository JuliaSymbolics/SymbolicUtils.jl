# Array interface, assumes that s.metadata is an ArrayShape, see below
# TODO: if shape is not known these should return Symbolic results
#
Base.axes(s::Symbolic{<:AbstractArray}) = axes(s.metadata)

Base.size(s::Symbolic{<:AbstractArray}) = map(length, axes(s))

function Base.getindex(x::Symbolic{T}, idx::Int...) where {T<:AbstractArray}
    Term{eltype(T)}(getindex, idx...)
end

maybe(f, x) = x === nothing ? nothing : f(x)

# allows promote_symtype to be called with the correct types
symtype(x::Union{Colon, AbstractRange}) = typeof(x)

function promote_symtype(::typeof(getindex), A, idx...)
    S = Core.Compiler.return_type(getindex,
                                  Tuple{A, idx...})
    if S != Union{} && (S <: AbstractArray || S <: eltype(A))
        return S
    end
    N = count(x->x <: Number, idx)
    N == ndims(A) ? eltype(A) : AbstractArray{eltype(A), ndims(A)-N}
end

function Base.getindex(x::Symbolic{A}, idx...) where {A<:AbstractArray}

    shape = maybe(m -> m[idx...], metadata(x))
    Term(getindex, shape, [x, idx...])
end


# ArrayShape
# Note: implement this as if it's an array
# the idea is it needs to be usable both during construction
# and simplification
struct ArrayShape{T, N}
    axes::Tuple
end

Base.axes(a::ArrayShape) = a.axes

function Base.getindex(a::ArrayShape{T}, idx...) where {T}
    axes = a.axes
    idx1 = to_indices(CartesianIndices(axes), axes, idx)
    newaxes = ([1:length(x) for x in idx1 if !(x isa Number)]...,)
    N = length(newaxes)
    newshape = ArrayShape{T, N}(newaxes)
end
