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
defaultval(::Type{UnitRange{Int}}) = 1:0
defaultval(::Type{Any}) = nothing

_unreachable() = error("Unreachable reached.")

Base.@propagate_inbounds function Base.getindex(x::Backing, i::Int)
    @boundscheck 1 <= i <= x.len
    if i == 1
        x.x1
    elseif i == 2
        x.x2
    elseif i == 3
        x.x3
    else
        _unreachable()
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

Base.@propagate_inbounds function Base.push!(x::Backing{T}, v::T) where {T}
    @boundscheck x.len < 3
    x.len += 1
    x[x.len] = v
    x
end

Base.@propagate_inbounds function Base.pop!(x::Backing{T}) where {T}
    @boundscheck x.len > 0
    v = x[x.len]
    x[x.len] = defaultval(T)
    x.len -= 1
    v
end

function Base.any(f::F, x::Backing) where {F <: Function}
    if x.len == 0
        return false
    elseif x.len == 1
        return f(x.x1)
    elseif x.len == 2
        return f(x.x1) || f(x.x2)
    elseif x.len == 3
        return f(x.x1) || f(x.x2) || f(x.x3)
    end
    _unreachable()
end

function Base.all(f::F, x::Backing) where {F <: Function}
    if x.len == 0
        return true
    elseif x.len == 1
        return f(x.x1)
    elseif x.len == 2
        return f(x.x1) && f(x.x2)
    elseif x.len == 3
        return f(x.x1) && f(x.x2) && f(x.x3)
    end
    _unreachable()
end

function Base.map(f::F, x::Backing{T}) where {F, T}
    if x.len == 0
        # StaticArrays does this, so we are only as bad as they are
        return Backing{Core.Compiler.return_type(f, Tuple{T})}()
    elseif x.len == 1
        x1 = f(x.x1)
        return Backing{typeof(x1)}(x1)
    elseif x.len == 2
        x1 = f(x.x1)
        x2 = f(x.x2)
        return Backing{Base.promote_typejoin(typeof(x1), typeof(x2))}(x1, x2)
    elseif x.len == 3
        x1 = f(x.x1)
        x2 = f(x.x2)
        x3 = f(x.x3)
        _T = Base.promote_typejoin(typeof(x1), typeof(x2))
        _T = Base.promote_typejoin(_T, typeof(x3))
        return Backing{_T}(x1, x2, x3)
    end
    _unreachable()
end

function Base.empty!(x::Backing{T}) where {T}
    x.x1 = defaultval(T)
    x.x2 = defaultval(T)
    x.x3 = defaultval(T)
    x.len = 0
    return x
    # if x.len >= 1
    #     x.x1 = defaultval(T)
    # end
    # if x.len >= 2
    #     x.x2 = defaultval(T)
    # end
    # if x.len == 3
    #     x.x3 = defaultval(T)
    # end
    # x.len = 0
    # return x
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
    _unreachable()
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

function Base.hash(x::Backing{T}, h::UInt) where {T}
    h += Base.hash_abstractarray_seed
    h = hash((1,), h)
    h = hash((3,), h)
    if x.len == 1
        h = hash(x.x1, h)
    elseif x.len == 2
        h = hash(x.x1, h)
        h = hash(x.x2, h)
    elseif x.len == 3
        h = hash(x.x1, h)
        h = hash(x.x2, h)
        h = hash(x.x3, h)
    end
    return h
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


Base.size(x::SmallVec) = size(x.data)
Base.isempty(x::SmallVec) = isempty(x.data)
Base.@propagate_inbounds Base.getindex(x::SmallVec, i::Int) = x.data[i]
Base.@propagate_inbounds Base.setindex!(x::SmallVec, v, i::Int) = setindex!(x.data, v, i)
Base.@propagate_inbounds function Base.getindex(x::SmallVec{T, V}, i::Vector{Int}) where {T, V}
    SmallVec{T, V}(x.data[i])
end

Base.@propagate_inbounds function Base.push!(x::SmallVec{T, V}, v::T) where {T, V}
    buf = x.data
    if buf isa V
        push!(buf, v)
        return x
    elseif buf isa Backing{T}
        if !isfull(buf)
            push!(buf, v)
            return x
        end
        buf = x.data = V(buf)::V
        push!(buf, v)
        return x
    end
    _unreachable()
end

Base.@propagate_inbounds Base.pop!(x::SmallVec) = pop!(x.data)

function Base.sizehint!(x::SmallVec{T, V}, n::Int; kwargs...) where {T, V}
    x.data isa Backing && return x
    sizehint!(x.data, n; kwargs...)
    x
end

Base.iterate(x::SmallVec) = iterate(x.data)
Base.iterate(x::SmallVec, st::Int) = iterate(x.data, st)
Base.any(f::F, x::SmallVec) where {F <: Function} = any(f, x.data)
Base.all(f::F, x::SmallVec) where {F <: Function} = all(f, x.data)
function Base.map(f::F, x::SmallVec{T, Vector{T}}) where {F, T}
    arr = map(f, x.data)
    SmallVec{eltype(arr),Vector{eltype(arr)}}(arr)
end
Base.empty!(x::SmallVec) = empty!(x.data)
Base.copy(x::SmallVec{T, V}) where {T, V} = SmallVec{T, V}(copy(x.data))
function Base.resize!(x::SmallVec{T, V}, sz::Integer) where {T, V}
    tmp = x.data
    if tmp isa Backing{T}
        if sz > 3
            tmp = x.data = V(tmp)
            resize!(tmp, sz)
        else
            resize!(tmp, sz)
        end
    else
        resize!(tmp, sz)
    end
    resize!(x.data, sz)
end
function Base.insert!(x::SmallVec{T, V}, i::Integer, val) where {T, V}
    if x.data isa Backing{T} && isfull(x.data)
        x.data = V(x.data)
    end
    insert!(x.data, i, val)
    return x
end
function Base.hash(x::SmallVec{T, V}, h::UInt) where {T, V}
    return hash(x.data, h)
end

backingtype(::Type{SmallVec{T, V}}) where {T, V} = Backing{T}
backingtype(x::SmallVec) = backingtype(typeof(x))
buffertype(::Type{SmallVec{T, V}}) where {T, V} = V
buffertype(x::SmallVec) = buffertype(typeof(x))

macro union_split_smallvec(svec::Symbol, body)
    svec = esc(svec)
    quote
        inner = $(svec).data
        if inner isa $backingtype($svec)
            let $svec = inner
                $(esc(body))
            end
        elseif inner isa $buffertype($svec)
            let $svec = inner
                $(esc(body))
            end
        else
            $_unreachable()
        end
    end
end
