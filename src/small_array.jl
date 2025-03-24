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

Base.@propagate_inbounds function Base.getindex(x::Backing, i::Int)
    @boundscheck 1 <= i <= x.len
    if i == 1
        x.x1
    elseif i == 2
        x.x2
    elseif i == 3
        x.x3
    end
end

Base.@propagate_inbounds function Base.setindex!(x::Backing, v, i::Int)
    @boundscheck 1 <= i <= x.len
    if i == 1
        setfield!(x, :x1, v)
    elseif i == 2
        setfield!(x, :x2, v)
    elseif i == 3
        setfield!(x, :x3, v)
    end
end

Base.@propagate_inbounds function Base.push!(x::Backing, v)
    x.len < 3 || throw(ArgumentError("`Backing` is full"))
    x.len += 1
    x[x.len] = v
end

Base.@propagate_inbounds function Base.pop!(x::Backing{T}) where {T}
    x.len > 0 || throw(ArgumentError("Array is empty"))
    v = x[x.len]
    x[x.len] = defaultval(T)
    x.len -= 1
    v
end

Base.@propagate_inbounds function Base.deleteat!(x::Backing{T}, i::Int) where {T}
    @boundscheck 1 <= i <= x.len
    x[i] = defaultval(T)
    for j in i:x.len-1
        x[i] = x[i + 1]
    end
    x.len -= 1
    x
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
Base.@propagate_inbounds Base.getindex(x::SmallVec, i::Int) = x.data[i]
Base.@propagate_inbounds Base.setindex!(x::SmallVec, v, i::Int) = setindex!(x.data, v, i)
Base.@propagate_inbounds Base.deleteat!(x::SmallVec, i) = deleteat!(x.data, i)

Base.@propagate_inbounds function Base.push!(x::SmallVec{T, V}, v) where {T, V}
    buf = x.data
    buf isa Backing{T} || return push!(buf::V, v)
    isfull(buf) || return push!(buf::Backing{T}, v)
    x.data = V(buf)
    return push!(x.data::V, v)
end

Base.@propagate_inbounds Base.pop!(x::SmallVec) = pop!(x.data)

function Base.sizehint!(x::SmallVec{T, V}, n; kwargs...) where {T, V}
    if x.data isa Backing
        if n > 3
            x.data = V(x.data)
        end
        return x
    end
    sizehint!(x.data, n; kwargs...)
    x
end

mutable struct LittleBigDict{K, V, KVec, VVec, D <: AbstractDict{K, V}} <: AbstractDict{K, V}
    data::Union{LittleDict{K, V, SmallVec{K, KVec}, SmallVec{V, VVec}}, D}

    function LittleBigDict{K, V, Kv, Vv, D}(keys, vals) where {K, V, Kv, Vv, D}
        nk = length(keys)
        nv = length(vals)
        nk == nv || throw(ArgumentError("Got $nk keys for $nv values"))
        if nk < 25
            keys = SmallVec{K, Kv}(keys)
            vals = SmallVec{V, Vv}(vals)
            new{K, V, Kv, Vv, D}(LittleDict{K, V}(keys, vals))
        else
            new{K, V, Kv, Vv, D}(D(zip(keys, vals)))
        end
    end

    function LittleBigDict{K, V, Kv, Vv, D}(d::D) where {K, V, Kv, Vv, D}
        if length(d) < 25
            return LittleBigDict{K, V, Kv, Vv, D}(collect(keys(d)), collect(values(d)))
        else
            return new{K, V, Kv, Vv, D}(d)
        end
    end

    function LittleBigDict{K, V, Kv, Vv, D}(d::AbstractDict) where {K, V, Kv, Vv, D}
        LittleBigDict{K, V, Kv, Vv, D}(collect(keys(d)), collect(values(d)))
    end
end

function LittleBigDict{K, V, D}() where {K, V, D}
    LittleBigDict{K, V, Vector{K}, Vector{V}, D}((), ())
end
LittleBigDict{K, V}() where {K, V} = LittleBigDict{K, V, Dict{K, V}}()

Base.haskey(x::LittleBigDict, k) = haskey(x.data, k)
Base.length(x::LittleBigDict) = length(x.data)
Base.getkey(x::LittleBigDict, k, d) = getkey(x.data, k, d)
Base.get(x::LittleBigDict, k, d) = get(x.data, k, d)
function Base.sizehint!(x::LittleBigDict{K, V, Kv, Vv, D}, n; kwargs...) where {K, V, Kv, Vv, D}
    if x.data isa LittleDict && n >= 25
        x.data = D(x.data)
    end
    sizehint!(x.data, n; kwargs...)
end
function Base.setindex!(x::LittleBigDict{K, V, Kv, Vv, D}, v, k) where {K, V, Kv, Vv, D}
    if x.data isa LittleDict
        delete!(x.data, k)
        get!(Returns(v), x.data, k)
        if length(x.data) > 25
            x.data = D(x.data)
        end
        v
    else
        setindex!(x.data, v, k)
    end
end
Base.getindex(x::LittleBigDict, k) = getindex(x.data, k)
Base.delete!(x::LittleBigDict, k) = delete!(x.data, k)
function Base.get!(f::Base.Callable, x::LittleBigDict{K, V, Kv, Vv, D}, k) where {K, V, Kv, Vv, D}
    res = get!(f, x.data, k)
    if x.data isa LittleDict && length(x.data) > 25
        x.data = D(x.data)
    end
    res
end
Base.iterate(x::LittleBigDict, args...) = iterate(x.data, args...)
