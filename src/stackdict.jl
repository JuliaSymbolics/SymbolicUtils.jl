"""
    StackDict{K, V}

A dictionary that only allows inserting new keys (not updating existing ones).
Keys are tracked in insertion order. Deletion is only permitted for the most
recently inserted key (stack discipline).
"""
struct StackDict{K, V}
    dict::Dict{K, V}
    keys::Vector{K}
end

StackDict{K, V}() where {K, V} = StackDict{K, V}(Dict{K, V}(), Vector{K}())

Base.length(sd::StackDict) = length(sd.keys)
Base.isempty(sd::StackDict) = isempty(sd.keys)

# Returns the last inserted key.
Base.lastindex(sd::StackDict) = last(sd.keys)

function Base.insert!(sd::StackDict, key, value)
    @assert !haskey(sd.dict, key)
    sd.dict[key] = value
    push!(sd.keys, key)
    return sd
end

function Base.empty!(sd::StackDict)
    empty!(sd.dict)
    empty!(sd.keys)
    return sd
end

# Only the last inserted key may be deleted.
function Base.delete!(sd::StackDict, key)
    @assert !isempty(sd.keys) && last(sd.keys) == key
    pop!(sd.keys)
    delete!(sd.dict, key)
    return sd
end

Base.get(sd::StackDict, key, default) = get(sd.dict, key, default)
