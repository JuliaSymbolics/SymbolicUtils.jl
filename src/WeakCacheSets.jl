# These can be changed, to trade off better performance for space
const maxallowedprobe = 16
const maxprobeshift   = 6

if VERSION < v"1.11"
    const Memory = Vector
end

"""
    WeakCacheSet()

`WeakCacheSet{K}()` constructs a cache of items of type `K` which are auto-deleted when dead.
Keys are compared with [`isequal`](@ref) and hashed with [`hash`](@ref).

!!! warning

    Keys are allowed to be mutable, but if you do mutate stored
    keys, the hash table may become internally inconsistent, in which case
    the `WeakCacheSet` will not work properly.

"""
mutable struct WeakCacheSet{K}
    # Metadata: empty => 0x00, full or removed => 0b1[7 most significant hash bits]
    slots::Memory{UInt8}
    keys::Memory{WeakRef}
    count::Int
    maxprobe::Int

    function WeakCacheSet{K}() where K
        n = 0
        slots = Memory{UInt8}(undef,n)
        fill!(slots, 0x0)
        keys = Memory{WeakRef}(undef, n)
        fill!(keys, WeakRef(nothing))
        new(slots, keys, 0, 0)
    end
end

# Gets 7 most significant bits from the hash (hsh), first bit is 1
_shorthash7(hsh::UInt) = (hsh >> (8sizeof(UInt)-7))%UInt8 | 0x80

# hashindex (key, sz) - computes optimal position and shorthash7
#     idx - optimal position in the hash table
#     sh::UInt8 - short hash (7 highest hash bits)
function hashindex(key, sz)
    hsh = hash2(key)::UInt
    idx = (((hsh % Int) & (sz-1)) + 1)::Int
    return idx, _shorthash7(hsh)
end

Base.@propagate_inbounds isslotempty(h::WeakCacheSet, i::Int) = h.slots[i] == 0x00
Base.@propagate_inbounds function isslotfilled(h::WeakCacheSet, i::Int)
    return (h.slots[i] != 0) && !isnothing(h.keys[i].value)
end
Base.@propagate_inbounds function isslotmissing(h::WeakCacheSet, i::Int)
    return isnothing(h.keys[i].value)
end
_tablesz(x::T) where T <: Integer = x < 16 ? T(16) : one(T)<<(Base.top_set_bit(x-one(T)))
function rehash!(h::WeakCacheSet{K}, newsz = length(h.keys)) where K
    olds = h.slots
    oldk = h.keys
    sz = length(olds)
    newsz = _tablesz(newsz)
    if h.count == 0
        # TODO: tryresize
        h.slots = Memory{UInt8}(undef, newsz)
        fill!(h.slots, 0x0)
        h.keys = Memory{WeakRef}(undef, newsz)
        fill!(h.keys, WeakRef(nothing))
        h.maxprobe = 0
        return h
    end

    slots = Memory{UInt8}(undef, newsz)
    fill!(slots, 0x0)
    keys = Memory{WeakRef}(undef, newsz)
    fill!(keys, WeakRef(nothing))
    count = 0
    maxprobe = 0

    for i = 1:sz
        @inbounds if olds[i] != 0
            k = oldk[i].value::Union{K, Nothing}
            isnothing(k) && continue
            index, sh = hashindex(k, newsz)
            index0 = index
            while slots[index] != 0
                index = (index & (newsz-1)) + 1
            end
            probe = (index - index0) & (newsz-1)
            maxprobe = max(maxprobe, probe)
            slots[index] = olds[i]
            keys[index] = WeakRef(k)
            count += 1
        end
    end

    h.slots = slots
    h.keys = keys
    h.count = count
    h.maxprobe = maxprobe
    return h
end

function Base.sizehint!(d::WeakCacheSet{T}, newsz; shrink::Bool=true) where T
    oldsz = length(d.slots)
    # limit new element count to max_values of the key type
    newsz = min(max(newsz, length(d)), Base.max_values(T)::Int)
    # need at least 1.5n space to hold n elements
    newsz = _tablesz(cld(3 * newsz, 2))
    return (shrink ? newsz == oldsz : newsz <= oldsz) ? d : rehash!(d, newsz)
end

# get (index, sh) for the key
#     index - where a key is stored, or -pos if not present
#             and the key would be inserted at pos
#     sh::UInt8 - short hash (7 highest hash bits)
function ht_keyindex2_shorthash!(h::WeakCacheSet{K}, key) where K
    sz = length(h.keys)
    if sz == 0 # if Dict was empty resize and then return location to insert
        rehash!(h, 4)
        index, sh = hashindex(key, length(h.keys))
        return -index, sh
    end
    iter = 0
    maxprobe = h.maxprobe
    index, sh = hashindex(key, sz)
    avail = 0
    keys = h.keys

    @inbounds while true
        if isslotempty(h,index)
            return (avail < 0 ? avail : -index), sh
        end

        if isslotmissing(h,index)
            if avail == 0
                # found an available slot, but need to keep scanning
                # in case "key" already exists in a later collided slot.
                avail = -index
            end
        elseif h.slots[index] == sh
            k = keys[index].value
            if key === k || isequal_with_metadata(key, k)
                return index, sh
            end
        end

        index = (index & (sz-1)) + 1
        iter += 1
        iter > maxprobe && break
    end

    avail < 0 && return avail, sh

    maxallowed = max(maxallowedprobe, sz>>maxprobeshift)
    # Check if key is not present, may need to keep searching to find slot
    @inbounds while iter < maxallowed
        if !isslotfilled(h,index)
            h.maxprobe = iter
            return -index, sh
        end
        index = (index & (sz-1)) + 1
        iter += 1
    end

    rehash!(h, h.count > 64000 ? sz*2 : sz*4)

    return ht_keyindex2_shorthash!(h, key)
end

Base.@propagate_inbounds function _setindex!(h::WeakCacheSet, key, index, sh = _shorthash7(hash2(key)))
    h.slots[index] = sh
    h.keys[index] = WeakRef(key)
    h.count += !isslotmissing(h, index)

    sz = length(h.keys)
    # Rehash now if necessary
    if h.count*3 > sz*2
        # > 2/3 full (including tombstones)
        rehash!(h, h.count > 64000 ? h.count*2 : max(h.count*4, 4))
    end
    nothing
end

function getkey!(h::WeakCacheSet{K}, key0) where K
    if key0 isa K
        key = key0
    else
        key = convert(K, key0)::K
        if !(isequal_with_metadata(key, key0)::Bool)
            throw(KeyTypeError(K, key0))
        end
    end
    getkey!(h, v0, key)
end

function getkey!(h::WeakCacheSet{K}, key::K) where K
    index, sh = ht_keyindex2_shorthash!(h, key)
    if index > 0
        foundkey = h.keys[index].value::Union{K, Nothing}
        if isnothing(foundkey)
            @inbounds h.keys[index] = key
            return key
        end
        return foundkey
    else
        @inbounds _setindex!(h, key, -index, sh)
        return key
    end
end

function Base.show(io::IO, t::WeakCacheSet{K}) where K
    recur_io = IOContext(io, :SHOWN_SET => t,
                             :typeinfo => K)

    limit = get(io, :limit, false)::Bool
    print(io, "WeakCacheSet(")
        n = 0
        first = true
        for val in t.keys
            realval = val.value::Union{K, Nothing}
            isnothing(realval) && continue
            first || print(io, ", ")
            first = false
            show(recur_io, realval)
            n+=1
            limit && n >= 10 && (print(io, "…"); break)
        end
    print(io, ')')
end
