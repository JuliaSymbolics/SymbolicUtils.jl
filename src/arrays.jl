struct ArrayShape{T, N}
    axes::Tuple
end

Base.axes(a::ArrayShape) = a.axes

Base.axes(s::Symbolic{<:AbstractArray}) = axes(s.metadata)

function Base.getindex(x::Symbolic{T}, idx::Int...) where {T<:AbstractArray}
    Term{eltype(T)}(getindex, idx...)
end

function Base.getindex(x::Symbolic{A}, idx...) where {T,M,A<:AbstractArray{T,M}}
    axes = metadata(x).axes
    idx = to_indices(CartesianIndices(axes), axes, idx)
    newaxes = ([1:length(x) for x in idx if !(x isa Number)]...,)
    N = length(newaxes)
    newshape = ArrayShape{T, N}(newaxes)

    S = Core.Compiler.return_type(getindex, Tuple{symtype(x), typeof.(idx)...})
    if S == Any || S == Union{}
        S = AbstractArray{T, N}
    end
    Term{S}(getindex, newshape, [x, idx...])
end
