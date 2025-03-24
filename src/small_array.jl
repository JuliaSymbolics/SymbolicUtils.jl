"""
    $(TYPEDEF)

A mutable resizeable 3-length vector to implement non-allocating small vectors.

$(TYPEDFIELDS)
"""
mutable struct Backing{T} <: AbstractVector{T}
    """
    Length of the buffer.
    """
    len::Int
    x1::T
    x2::T
    x3::T

    Backing{T}() where {T} = new{T}(0)
    Backing{T}(x1) where {T} = new{T}(1, x1)
    Backing{T}(x1, x2) where {T} = new{T}(2, x1, x2)
    Backing{T}(x1, x2, x3) where {T} = new{T}(3, x1, x2, x3)
end

Base.size(x::Backing) = (x.len,)
Base.isempty(x::Backing) = x.len == 0

"""
    $(TYPEDSIGNATURES)

Value to use when removing an element from a `Backing`. Used so stored entries can be
GC'ed when removed.
"""
defaultval(::Type{T}) where {T <: Number} = zero(T)
defaultval(::Type{Any}) = nothing

function Base.getindex(x::Backing, i::Int)
    @boundscheck 1 <= i <= x.len
    if i == 1
        x.x1
    elseif i == 2
        x.x2
    elseif i == 3
        x.x3
    end
end

function Base.setindex!(x::Backing, v, i::Int)
    @boundscheck 1 <= i <= x.len
    if i == 1
        setfield!(x, :x1, v)
    elseif i == 2
        setfield!(x, :x2, v)
    elseif i == 3
        setfield!(x, :x3, v)
    end
end

function Base.push!(x::Backing, v)
    x.len < 3 || throw(ArgumentError("`Backing` is full"))
    x.len += 1
    x[x.len] = v
end

function Base.pop!(x::Backing{T}) where {T}
    x.len > 0 || throw(ArgumentError("Array is empty"))
    v = x[x.len]
    x[x.len] = defaultval(T)
    x.len -= 1
    v
end

"""
    $(TYPEDSIGNATURES)

Whether the `Backing` is full.
"""
isfull(x::Backing) = x.len == 3

"""
    $(TYPEDSIGNATURES)

A small-buffer-optimized `AbstractVector`. Uses a `Backing` when the number of elements
is within the size of `Backing`, and allocates a `V` when the number of elements exceed
this limit.
"""
mutable struct SmallVec{T, V <: AbstractVector{T}} <: AbstractVector{T}
    data::Union{Backing{T}, V}

    function SmallVec{T}(x::AbstractVector{T}) where {T}
        V = typeof(x)
        if length(x) < 4
            new{T, V}(Backing{T}(x...))
        else
            new{T, V}(x)
        end
    end

    function SmallVec{T, V}() where {T, V}
        new{T, V}(Backing{T}())
    end

    function SmallVec{T, V}(x::Union{Tuple, AbstractVector}) where {T, V}
        if length(x) <= 3
            new{T, V}(Backing{T}(x...))
        else
            new{T, V}(V(x isa Tuple ? collect(x) : x))
        end
    end
end

Base.convert(::Type{SmallVec{T, V}}, x::V) where {T, V} = SmallVec{T}(x)
Base.convert(::Type{SmallVec{T, V}}, x) where {T, V} = SmallVec{T}(V(x))
Base.convert(::Type{SmallVec{T, V}}, x::SmallVec{T, V}) where {T, V} = x

Base.size(x::SmallVec) = size(x.data)
Base.isempty(x::SmallVec) = isempty(x.data)
Base.getindex(x::SmallVec, i::Int) = x.data[i]
Base.setindex!(x::SmallVec, v, i::Int) = setindex!(x.data, v, i)

function Base.push!(x::SmallVec{T, V}, v) where {T, V}
    buf = x.data
    buf isa Backing{T} || return push!(buf::V, v)
    isfull(buf) || return push!(buf::Backing{T}, v)
    x.data = V(buf)
    return push!(x.data::V, v)
end

Base.pop!(x::SmallVec) = pop!(x.data)

function Base.sizehint!(x::SmallVec{T, V}, n; kwargs...) where {T, V}
    x.data isa Backing && return x
    sizehint!(x.data, n; kwargs...)
    x
end
