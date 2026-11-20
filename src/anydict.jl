# Dict view included into `module AnyNumbers` from `anynumber.jl`.

"""
    AnyNumberDict{K, D <: AbstractDict{K, AnyNumber}} <: AbstractDict{K, Number}

`AbstractDict` view over a dictionary whose values are [`AnyNumber`](@ref)s:
every read (`getindex`, `get`, `iterate`, `values`, `pairs`) unwraps the
stored wrapper, so consumers see the raw `Number` values the dictionary
contained before `AnyNumber` existed. The wrapped dictionary — which internal
code should prefer via [`Base.parent`](@ref) — keeps `AnyNumber` values so
merges hit the union-split arithmetic paths.

Construction accepts any `AbstractDict`: dictionaries already storing
`AnyNumber` values are wrapped as-is (preserving the dict type), others are
copied into a `Dict{K, AnyNumber}`.
"""
struct AnyNumberDict{K, D <: AbstractDict{K, AnyNumber}} <: AbstractDict{K, Number}
    dict::D
end

AnyNumberDict(d::AnyNumberDict) = d
AnyNumberDict{K, D}(kvs::Pair...) where {K, D <: AbstractDict{K, AnyNumber}} =
    AnyNumberDict{K, D}(D(kvs...))
AnyNumberDict{K, D}(kv::Pair) where {K, D <: AbstractDict{K, AnyNumber}} =
    AnyNumberDict{K, D}(D(kv))
function AnyNumberDict(d::AbstractDict{K}) where {K}
    if d isa AbstractDict{K, AnyNumber}
        return AnyNumberDict{K, typeof(d)}(d)
    else
        return AnyNumberDict{K, Dict{K, AnyNumber}}(Dict{K, AnyNumber}(d))
    end
end

Base.parent(d::AnyNumberDict) = d.dict

# `convert` lets the `BSImpl.AddMul` inner constructor coerce plain
# dictionaries into the declared field type like any other field.
function Base.convert(::Type{AnyNumberDict{K, D}}, d::AbstractDict{K}) where {K, D}
    d isa AnyNumberDict{K, D} && return d
    d isa AnyNumberDict && (d = parent(d))
    return AnyNumberDict{K, D}(d isa D ? d : D(d))
end

function Base.iterate(d::AnyNumberDict, state...)
    ret = iterate(d.dict, state...)
    ret === nothing && return nothing
    (k, v), st = ret
    return (k => _value(v), st)
end

Base.length(d::AnyNumberDict) = length(d.dict)
Base.isempty(d::AnyNumberDict) = isempty(d.dict)
Base.haskey(d::AnyNumberDict, k) = haskey(d.dict, k)
Base.getkey(d::AnyNumberDict, k, def) = getkey(d.dict, k, def)
Base.keys(d::AnyNumberDict) = keys(d.dict)
Base.values(d::AnyNumberDict) = (_value(v) for v in values(d.dict))
Base.eltype(::Type{<:AnyNumberDict{K}}) where {K} = Pair{K, Number}

function Base.getindex(d::AnyNumberDict, k)
    return _value(d.dict[k])
end

function Base.get(d::AnyNumberDict, k, def)
    v = get(d.dict, k, nothing)
    return v === nothing ? def : _value(v)
end

function Base.get!(d::AnyNumberDict, k, def)
    v = get!(d.dict, k, def isa AnyNumber ? def : _wrap(def))
    return _value(v)
end

function Base.setindex!(d::AnyNumberDict, v, k)
    d.dict[k] = v
    return d
end
Base.delete!(d::AnyNumberDict, k) = delete!(d.dict, k)
Base.pop!(d::AnyNumberDict, k) = _value(pop!(d.dict, k))
Base.pop!(d::AnyNumberDict, k, def) =
    haskey(d.dict, k) ? _value(pop!(d.dict, k)) : def
Base.empty!(d::AnyNumberDict) = empty!(d.dict)
Base.sizehint!(d::AnyNumberDict, n) = sizehint!(d.dict, n)
Base.copy(d::AnyNumberDict{K, D}) where {K, D} = AnyNumberDict{K, D}(copy(d.dict))
Base.empty(::AnyNumberDict{K, D}) where {K, D} = AnyNumberDict{K, D}(D())
