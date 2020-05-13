const SymArray{T,N} = Symbolic{<:AbstractArray{T,N}}

# Array interface, assumes that s.metadata is an ArrayShape, see below
# TODO: if shape is not known these should return Symbolic results
#
Base.axes(s::SymArray) = axes(s.metadata)

Base.size(s::SymArray) = map(length, axes(s))

Base.ndims(s::SymArray) = ndims(symtype(s))

function Base.getindex(x::Symbolic{T}, idx::Int...) where {T<:AbstractArray}
    Term{eltype(T)}(getindex, idx...)
end

maybe(f, x) = x === nothing ? nothing : f(x)

# allows promote_symtype to be called with the correct types
symtype(x::Union{Colon, AbstractRange}) = typeof(x)


# Partial information
elt(s::SymArray) = _eltype(symtype(s))
elt(::Type{<:AbstractArray{T}}) where {T} = T
elt(::Type{<:AbstractArray}) = nothing

nd(s::SymArray) = _ndims(symtype(s))
nd(::Type{<:AbstractArray{<:Any, N}}) where {N} = N
nd(::Type{<:AbstractArray}) = nothing

shape(s::SymArray) = metadata(s)

macro maybe(args...)
    f = args[end]
    vars = args[1:end-1]
    names = [(@assert v.head == :(=); v.args[1]) for v in vars]
    quote
        $(vars...)
        if !any(isnothing, ($(names...),))
            $f
        end
        # nothing otherwise
    end |> esc
end

function promote_symtype(::typeof(getindex),
                         A::Type{<:AbstractArray},
                         idx...)
    lessdims = count(x->x <: Number, idx)
    @maybe T=elt(A) begin
        @maybe N=nd(A) return AbstractArray{T,N-lessdims}
        return AbstractArray{T}
    end

    @maybe N=nd(A) return AbstractArray{T, N-lessdims} where T

    return AbstractArray
end

function Base.getindex(x::SymArray, idx...)
    shp = @maybe s=shape(x) s[idx...]
    Term(getindex, shp, [x, idx...])
end

# basic

function eltype(A::SymArray)
    @maybe T=elt(A) return T
    error("eltype of $A not known")
end

function length(A::SymArray)
    @maybe s=shape(A) return length(s)
    error("length of $A not known")
end

function ndims(A::SymArray)
    @maybe n=nd(A) return n
    @maybe s=shape(A) return length(s.axes)
    error("ndims of $A not known")
end

function size(A)
    @maybe s=shape(A) return length.(s.axes)
    error("size of $A not known")
end

function axes(A)
    @maybe s=shape(A) return s.axes
    error("axes of $A not known")
end

function eachindex(A)
    @maybe s=shape(A) CartesianIndices(s.axes)
    error("eachindex of $A not known")
end

# todo: stride?

# ArrayShape
# Note: implement this as if it's an array
# the idea is it needs to be usable both during construction
# and simplification

struct ArrayShape
    axes::Tuple
end

Base.axes(a::ArrayShape) = a.axes

function Base.getindex(a::ArrayShape, idx...)
    axes = a.axes
    idx1 = to_indices(CartesianIndices(axes), axes, idx)
    newaxes = ([1:length(x) for x in idx1 if !(x isa Number)]...,)
    newshape = ArrayShape(newaxes)
end
