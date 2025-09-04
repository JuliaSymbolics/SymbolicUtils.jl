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

Base.@propagate_inbounds function Base.getindex(x::Backing{T}, i::Vector{Int}) where {T}
    n = length(i)
    if n == 1
        return Backing{T}(x[i[1]])
    elseif n == 2
        return Backing{T}(x[i[1]], x[i[2]])
    elseif n == 3
        return Backing{T}(x[i[1]], x[i[2]], x[i[3]])
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
    @boundscheck x.len < 3
    x.len += 1
    x[x.len] = v
end

Base.@propagate_inbounds function Base.pop!(x::Backing{T}) where {T}
    @boundscheck x.len > 0
    v = x[x.len]
    x[x.len] = defaultval(T)
    x.len -= 1
    v
end

function Base.any(f::Function, x::Backing)
    if x.len == 0
        false
    elseif x.len == 1
        f(x.x1)
    elseif x.len == 2
        f(x.x1) || f(x.x2)
    elseif x.len == 3
        f(x.x1) || f(x.x2) || f(x.x3)
    end
end

function Base.all(f::Function, x::Backing)
    if x.len == 0
        true
    elseif x.len == 1
        f(x.x1)
    elseif x.len == 2
        f(x.x1) && f(x.x2)
    elseif x.len == 3
        f(x.x1) && f(x.x2) && f(x.x3)
    end
end

function Base.map(f, x::Backing{T}) where {T}
    if x.len == 0
        # StaticArrays does this, so we are only as bad as they are
        Backing{Core.Compiler.return_type(f, Tuple{T})}()
    elseif x.len == 1
        x1 = f(x.x1)
        Backing{typeof(x1)}(x1)
    elseif x.len == 2
        x1 = f(x.x1)
        x2 = f(x.x2)
        Backing{Base.promote_typejoin(typeof(x1), typeof(x2))}(x1, x2)
    elseif x.len == 3
        x1 = f(x.x1)
        x2 = f(x.x2)
        x3 = f(x.x3)
        _T = Base.promote_typejoin(typeof(x1), typeof(x2))
        _T = Base.promote_typejoin(_T, typeof(x3))
        Backing{_T}(x1, x2, x3)
    end
end

function Base.empty!(x::Backing{T}) where {T}
    if x.len >= 1
        x.x1 = defaultval(T)
    end
    if x.len >= 2
        x.x2 = defaultval(T)
    end
    if x.len == 3
        x.x3 = defaultval(T)
    end
    x.len = 0
    return x
end

function Base.copy(x::Backing{T}) where {T}
    if x.len == 0
        return Backing{T}()
    elseif x.len == 1
        return Backing{T}(x.x1)
    elseif x.len == 2
        return Backing{T}(x.x1, x.x2)
    elseif x.len == 3
        return Backing{T}(x.x1, x.x2, x.x3)
    end
end

function Base.resize!(x::Backing, sz::Integer)
    if sz > 3
        throw(ArgumentError("New length must be <= 3"))
    elseif sz < 0
        throw(ArgumentError("New length must be >= 0"))
    end
    x.len = sz
    return x
end

function Base.insert!(x::Backing{T}, i::Integer, val::T) where {T}
    @boundscheck !isfull(x)
    @boundscheck 1 <= i <= x.len + 1
    x.len += 1
    if x.len == 1 && i == 1
        x.x1 = val
    elseif x.len == 2 && i == 1
        x.x2 = x.x1
        x.x1 = val
    elseif x.len == 2 && i == 2
        x.x2 = val
    elseif x.len == 3 && i == 1
        x.x3 = x.x2
        x.x2 = x.x1
        x.x1 = val
    elseif x.len == 3 && i == 2
        x.x3 = x.x2
        x.x2 = val
    elseif x.len == 3 && i == 3
        x.x3 = val
    else
        error("Unreachable")
    end
    return x
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

    function SmallVec{T, V}(x::Backing{T}) where {T, V}
        new{T, V}(x)
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

    function SmallVec{T, V}(::UndefInitializer, n::Integer) where {T, V}
        if n <= 3
            inner = Backing{T}()
            inner.len = n
        else
            inner = V(undef, n)
        end
        return new{T, V}(inner)
    end
end

Base.convert(::Type{SmallVec{T, V}}, x::V) where {T, V} = SmallVec{T}(x)
Base.convert(::Type{SmallVec{T, V}}, x) where {T, V} = SmallVec{T}(V(x))
Base.convert(::Type{SmallVec{T, V}}, x::SmallVec{T, V}) where {T, V} = x

Base.size(x::SmallVec) = size(x.data)
Base.isempty(x::SmallVec) = isempty(x.data)
Base.@propagate_inbounds Base.getindex(x::SmallVec, i::Int) = x.data[i]
Base.@propagate_inbounds Base.setindex!(x::SmallVec, v, i::Int) = setindex!(x.data, v, i)
Base.@propagate_inbounds function Base.getindex(x::SmallVec{T, V}, i::Vector{Int}) where {T, V}
    SmallVec{T, V}(x.data[i])
end

Base.@propagate_inbounds function Base.push!(x::SmallVec{T, V}, v) where {T, V}
    buf = x.data
    buf isa Backing{T} || return push!(buf::V, v)
    isfull(buf) || return push!(buf::Backing{T}, v)
    x.data = V(buf)
    return push!(x.data::V, v)
end

Base.@propagate_inbounds Base.pop!(x::SmallVec) = pop!(x.data)

function Base.sizehint!(x::SmallVec{T, V}, n; kwargs...) where {T, V}
    x.data isa Backing && return x
    sizehint!(x.data, n; kwargs...)
    x
end

Base.any(f::Function, x::SmallVec) = any(f, x.data)
Base.all(f::Function, x::SmallVec) = all(f, x.data)
function Base.map(f, x::SmallVec{T, Vector{T}}) where {T}
    arr = map(f, x.data)
    SmallVec{eltype(arr),Vector{eltype(arr)}}(arr)
end
Base.empty!(x::SmallVec) = empty!(x.data)
Base.copy(x::SmallVec{T, V}) where {T, V} = SmallVec{T, V}(copy(x.data))
Base.resize!(x::SmallVec, sz::Integer) = resize!(x.data, sz)
function Base.insert!(x::SmallVec{T, V}, i::Integer, val) where {T, V}
    if x.data isa Backing{T} && isfull(x.data)
        x.data = V(x.data)
    end
    insert!(x.data, i, val)
    return x
end
