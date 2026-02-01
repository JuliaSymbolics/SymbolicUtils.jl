"""
    $(TYPEDEF)

Sentinel value used for a cache miss, since cached functions may return `nothing`.
"""
struct CacheSentinel end

mutable struct IDType end

"""
    $(TYPEDEF)

Struct wrapping the `id` of a `BasicSymbolic`, since arguments annotated
`::Union{BasicSymbolic, UInt}` would not be able to differentiate between looking
up a symbolic or a `UInt`.
"""
struct SymbolicKey
    id::IDType
end

"""
    $(TYPEDSIGNATURES)

The key stored in the cache for a particular value. Returns a `SymbolicKey` for
`BasicSymbolic` and is the identity function otherwise.
"""
# can't dispatch because `BasicSymbolic` isn't defined here
function get_cache_key(x)
    @nospecialize x
    if x isa BasicSymbolic{SymReal}
        id = x.id
        if id === nothing
            return CacheSentinel()
        end
        return SymbolicKey(id)
    elseif x isa BasicSymbolic{SafeReal}
        id = x.id
        if id === nothing
            return CacheSentinel()
        end
        return SymbolicKey(id)
    elseif x isa BasicSymbolic{TreeReal}
        id = x.id
        if id === nothing
            return CacheSentinel()
        end
        return SymbolicKey(id)
    else
        x
    end
end

"""
    associated_cache(fn)

Given a function annotated with `@cache`, get the cache struct it uses. Automatically
implemented by `@cache`.
"""
function associated_cache end

"""
    $(TYPEDSIGNATURES)

Set the maximum size for the cache associated with function `fn` to `limit`.
"""
function set_limit!(fn, limit::Int)
    cache = associated_cache(fn)
    cache.limit = limit
end

"""
    $(TYPEDSIGNATURES)

Get the maximum size for the cache associated with function `fn`.
"""
function get_limit(fn)
    associated_cache(fn).limit
end

"""
    $(TYPEDSIGNATURES)

Set the fraction of entries to retain on clear for the cache associated with
function `fn` to `retain_fraction`.
"""
function set_retain_fraction!(fn, retain_fraction::Float64)
    cache = associated_cache(fn)
    cache.retain_fraction = retain_fraction
end

"""
    $(TYPEDSIGNATURES)

Get the `retain_fraction` for the cache associated with function `fn`.
"""
function get_retain_fraction(fn)
    associated_cache(fn).retain_fraction
end

"""
    $(TYPEDSIGNATURES)

Enable or disable the caching of `fn` according to `state`.
"""
function toggle_caching!(fn, state::Bool)
    cache = associated_cache(fn)
    cache.enabled = state
end

"""
    $(TYPEDSIGNATURES)

Check whether caching is enabled for `fn`.
"""
function is_caching_enabled(fn)
    associated_cache(fn).enabled
end

"""
    $(TYPEDSIGNATURES)

Get the statistics for the cached function `fn`. This is task-specific.

See also: [`SymbolicUtils.CacheStats`](@ref).
"""
function get_stats(fn)
    associated_cache(fn).tlv[][2]
end

"""
    $(TYPEDSIGNATURES)

Clear the cache for [`SymbolicUtils.@cache`](@ref)d function `fn`. This is task specific.
Also resets the stats.
"""
function clear_cache!(fn)
    dict, stats = associated_cache(fn).tlv[]
    empty!(dict)
    sizehint!(dict, get_limit(fn))
    reset_stats!(stats)
end

"""
    $(TYPEDEF)

Track statistics about a cached function.

# Fields

$(TYPEDFIELDS)
"""
mutable struct CacheStats
    """
    The number of cache hits.
    """
    hits::Int
    """
    The number of cache misses.
    """
    misses::Int
    """
    The number of times the cache has been randomly cleared.
    """
    clears::Int
end

CacheStats() = CacheStats(0, 0, 0)

"""
    $(TYPEDSIGNATURES)

Reset the tracked statistics for a cache.
"""
function reset_stats!(stats::CacheStats)
    stats.hits = 0
    stats.misses = 0
    stats.clears = 0
end

"""
    $(TYPEDSIGNATURES)

Reset the tracked statistics for cached function `fn`.
"""
function reset_stats!(fn)
    reset_stats!(get_stats(fn))
end

"""
    @cache [options...] function foo(arg1::Type, arg2::Type; kwargs...)::ReturnType
        # ...
    end

Create a cached version of the function `foo`. This is typically useful for recursive
functions that descend through an expression tree.

The return type of the function should be annotated to avoid warnings. If any of the
argument types is a `BasicSymbolic`, uses a special caching for efficiency. If an argument
has `Any` type or a `Union` containing `BasicSymbolic`, a runtime check is performed to
handle it. This can be avoided if the type is annotated with `BasicSymbolic`. The maximum
number of entries in the cache can be set using the `limit` option by providing an
integer size. This defaults to `100_000`. When this limit is hit, a fraction of the
entries in the cache will be cleared at random. The fraction of entries retained is given
by the `retain_fraction` option, which defaults to `0.5`.

Multiple methods of the same function cannot be cached and will lead to an error. This
should be avoided by creating a wrapper function which calls the one with ,multiple
methods, and caching the wrapper. The function with multiple methods should recursively
call the wrapper. Caching a single method is valid.

The cache is thread-safe and uses TaskLocalValues.jl to maintain a task-specific cache.

The caching behavior for this function is enabled by default. Use the `enabled` option
to toggle this.

See also: [`SymbolicUtils.get_limit`](@ref), [`SymbolicUtils.set_limit!`](@ref),
[`SymbolicUtils.get_retain_fraction`](@ref), [`SymbolicUtils.set_retain_fraction!`](@ref),
[`SymbolicUtils.toggle_caching!`](@ref), [`SymbolicUtils.is_caching_enabled`](@ref),
[`SymbolicUtils.get_stats`](@ref), [`SymbolicUtils.clear_cache!`](@ref),
[`SymbolicUtils.reset_stats!`](@ref).
"""
macro cache(args...)
    # the last argument is the function expression, all prior arguments are
    # config options of the form `key = value`
    fnexpr = last(args)
    configargs = Base.front(args)

    # parse configuration options
    config = Dict(:limit => 100_000, :retain_fraction => 0.5, :allow_any_return => false, :enabled => true)
    for carg in configargs
        if !Meta.isexpr(carg, :(=))
            throw(ArgumentError("Expected `key = value` syntax, got $carg"))
        end
        k, v = carg.args

        if !haskey(config, k)
            throw(ArgumentError(
                "Expected option to be one of $(collect(keys(config))), got $k"))
        end
        if typeof(v) != typeof(config[k])
            exT = typeof(config[k])
            vT = typeof(v)
            throw(ArgumentError(
                "Expected a value of type $exT for option $k, got $v of type $vT."))
        end
        config[k] = v
    end

    # Parse the function. This also throws a nice error if it isn't a valid function
    fn = EL.JLFunction(fnexpr)
    name = fn.name
    # this will now be an inner workhorse function, which the cached function will call
    fn.name = gensym(Symbol(name))
    # the name of the global constant cache
    cachename = Symbol("cacheof($name)")
    # conditions for performing caching. At the very least, need hashconsing enabled and
    # caching for this function is enabled.
    conditions = :($(@__MODULE__).ENABLE_HASHCONSING[] && $cachename.enabled)
    # They keys of the cache are arguments to the function, this is a list of expressions
    # of those arguments. This isn't just the arguments to the function since the key
    # for symbolic objects will be the ID
    keyexprs = []
    # The types of the arguments, matching the order in `keyexprs`
    keytypes = []
    # The arguments of the workhorse function
    argexprs = []
    # The name of the variable storing the result of looking up the cache
    cache_value_name = :val
    valid_key_condition = :(true)
    # The condition for a cache hit
    cache_hit_condition = :(!($cache_value_name isa $CacheSentinel))

    for arg in fn.args
        # handle arguments with defaults
        if Meta.isexpr(arg, :kw)
            arg = arg.args[1]
        end
        if Meta.isexpr(arg, :...)
            arg = arg.args[1]
            if Meta.isexpr(arg, :(::))
                argname = arg.args[1]
            else
                argname = arg
            end
            push!(keyexprs, :($get_cache_key.($argname)...))
            push!(argexprs, Expr(:..., argname))
            push!(keytypes, Vararg)
            valid_key_condition = :($valid_key_condition && !any(i -> key[i] isa $CacheSentinel, $(length(keyexprs)):length(key)))
            continue
        end
        if !Meta.isexpr(arg, :(::))
            # if the type is `Any`, branch on it being a `BasicSymbolic`
            push!(keyexprs, :($get_cache_key($arg)))
            push!(argexprs, arg)
            push!(keytypes, Any)
            valid_key_condition = :($valid_key_condition && !($(Symbol(:key_, length(keyexprs))) isa $CacheSentinel))
            continue
        end
        argname, Texpr = arg.args
        push!(argexprs, argname)

        if Texpr == :Any
            # if the type is `Any`, branch on it being a `BasicSymbolic`
            push!(keyexprs, :($get_cache_key($argname)))
            push!(keytypes, Any)
            valid_key_condition = :($valid_key_condition && !($(Symbol(:key_, length(keyexprs))) isa $CacheSentinel))
            continue
        end

        # handle Union types that may contain a `BasicSymbolic`
        if Meta.isexpr(Texpr, :curly) && Texpr.args[1] == :Union
            Texprs = Texpr.args[2:end]
            Ts = map(Base.Fix1(Base.eval, __module__), Texprs)
            keyTs = map(x -> x <: BasicSymbolic ? SymbolicKey : x, Ts)
            maybe_basicsymbolic = any(x -> x <: BasicSymbolic, Ts)
            push!(keytypes, Union{keyTs...})
            if maybe_basicsymbolic
                push!(keyexprs, :($get_cache_key($argname)))
                valid_key_condition = :($valid_key_condition && !($(Symbol(:key_, length(keyexprs))) isa $CacheSentinel))
            else
                push!(keyexprs, argname)
            end
            continue
        end
            
        # use `eval` to get the type because we need to know if it's a `BasicSymbolic`
        T = Base.eval(__module__, Texpr)
        if T <: BasicSymbolic
            push!(keytypes, SymbolicKey) 
            push!(keyexprs, :($get_cache_key($argname)))
            valid_key_condition = :($valid_key_condition && !($(Symbol(:key_, length(keyexprs))) isa $CacheSentinel))
        else
            push!(keytypes, T)
            push!(keyexprs, argname)
        end
    end

    # the expression for getting the keys
    keyvarsexpr = Expr(:block)
    for (i, kex) in enumerate(keyexprs)
        kname = Symbol(:key_, i)
        if Meta.isexpr(kex, :...)
            push!(keyvarsexpr.args, :($kname = ($kex,)))
            keyexprs[i] = :($kname...)
        else
            push!(keyvarsexpr.args, :($kname = $kex))
            keyexprs[i] = kname
        end
    end

    is_singleton_key = false
    if length(keyexprs) == 1 && !Meta.isexpr(keyexprs[1], :...)
        keyexpr = only(keyexprs)
        keytypes = only(keytypes)
        is_singleton_key = true
    else
        keyexpr = EL.xtuple(keyexprs...)
    end

    rettype = fn.rettype
    if rettype === nothing
        if !config[:allow_any_return]
            @warn "`Any` return type detected. This leads to a type-unstable cache. Disable this warning by providing `allow_any_return = true` to `SymbolicUtils.@cache`."
        end
        rettype = Any
    end

    # construct an expression for the type of the cache keys
    if is_singleton_key
        keyT = keytypes
    else
        keyT = Expr(:curly, Tuple)
        append!(keyT.args, keytypes)
    end
    valT = rettype
    # the type of the cache
    cacheT = :(Dict{$keyT, $valT})
    # type of the `TaskLocalValue`
    tlvT = :($(TaskLocalValue){Tuple{$cacheT, $CacheStats}})
    # the name of the cache struct
    # this uses the name of the function so that trying to `@cache` two methods
    # of the same function results in a struct re-definition error
    structT = Symbol("cacheof($name)_type")
    # mutable to allow changing max size
    structdef = EL.JLStruct(; name = structT, ismutable = true)

    # struct fields
    push!(structdef.fields, EL.JLField(; name = :tlv, type = tlvT, isconst = true))
    push!(structdef.fields, EL.JLField(; name = :limit, type = Int, isconst = false))
    push!(structdef.fields, EL.JLField(; name = :retain_fraction, type = Float64, isconst = false))
    push!(structdef.fields, EL.JLField(; name = :enabled, type = Bool, isconst = false))

    # the struct itself is callable, acting as a filter function for emptying the cache
    filterfn = EL.JLFunction(; name = :(cache::$structT), args = [:kvp])
    filterfn.body = :(begin
        rand() <= cache.retain_fraction
    end)

    # instantiation of the TaskLocalValue
    tlvctor = :($tlvT(() -> ((dict = $cacheT(); sizehint!(dict, $get_limit($name)); dict), $CacheStats())))
    # instantiation expression for the constant value
    cachector = Expr(:call, structT, tlvctor, config[:limit], config[:retain_fraction], config[:enabled])

    # call to the workhorse function
    innercall = EL.codegen_ast(EL.JLCall(fn.name, argexprs, fn.kwargs))

    # wrapper which takes the name of the cached function
    wrapperfn = EL.JLFunction(; name = name, args = fn.args, kwargs = fn.kwargs)
    wrapperfn.body = :(begin
        # if we can cache
        if $conditions
            $keyvarsexpr
            # construct the `Tuple` key
            key = $keyexpr
            if !($valid_key_condition)
                return $innercall
            end
            # get the cache and stats from the `TaskLocalValue` to avoid accessing
            # `task_local_storage` repeatedly.
            cachedict, cachestats = $cachename.tlv[]
            # look it up
            # we use a custom sentinel value since `nothing` is a valid return value
            # which we might want to cache
            $cache_value_name = $(get)(cachedict, key, $(CacheSentinel)())
            if $cache_hit_condition
                # cache hit
                cachestats.hits += 1
                return $cache_value_name
            end
            # cache miss
            cachestats.misses += 1
            val = $innercall
            # filter if oversized
            if length(cachedict) >= $cachename.limit
                cachestats.clears += 1
                $(filter!)($cachename, cachedict)
            end
            # add to cache
            cachedict[key] = $cache_value_name
            return $cache_value_name
        end

        # if we're not doing caching
        return $innercall
    end)

    return quote
        $(EL.codegen_ast(structdef))
        $(EL.codegen_ast(filterfn))
        
        const $cachename = $cachector

        $(EL.codegen_ast(fn))
        Base.@__doc__ $(EL.codegen_ast(wrapperfn))

        function (::$(typeof(associated_cache)))(::typeof($name))
            $cachename
        end
    end |> esc
end
