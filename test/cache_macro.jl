using SymbolicUtils
using SymbolicUtils: BasicSymbolic, @cache, associated_cache, set_limit!, get_limit,
                     clear_cache!, SymbolicKey, metadata, maketerm
using OhMyThreads: tmap

@cache function f1(x::BasicSymbolic)::BasicSymbolic
    return 2x + 1
end

@testset "::BasicSymbolic" begin
    @syms x
    val = f1(x)
    @test isequal(val, 2x + 1)
    cachestruct = associated_cache(f1)
    cache, stats = cachestruct.tlv[]
    @test cache isa Dict{Tuple{SymbolicKey}, BasicSymbolic}
    @test length(cache) == 1
    @test cache[(SymbolicKey(objectid(x)),)] === val
    @test stats.hits == 0
    @test stats.misses == 1
    f1(x)
    @test stats.hits == 1
    @test stats.misses == 1

    xx = setmetadata(x, Int, 0)
    val = f1(xx)
    @test length(cache) == 2
    @test stats.misses == 2

    set_limit!(f1, 10)
    @test get_limit(f1) == 10
    for i in 1:8
        xx = setmetadata(xx, Int, i)
        f1(xx)
        @test length(cache) == i + 2
    end
    xx = setmetadata(xx, Int, 9)
    f1(xx)
    @test length(cache) < 10
    @test stats.clears == 1

    hits = stats.hits
    misses = stats.misses
    len = length(cache)

    @syms x::Float64 # different symtype
    val = f1(x)
    @test length(cache) == len + 1
    @test stats.hits == hits
    @test stats.misses == misses + 1
    @test f1(x) === val
    @test stats.hits == hits + 1
    
    clear_cache!(f1)
    @test length(cache) == 0
    stats = SymbolicUtils.get_stats(f1)
    @test stats.hits == stats.misses == stats.clears == 0
    SymbolicUtils.set_retain_fraction!(f1, 0.1)
    @test SymbolicUtils.get_retain_fraction(f1) == 0.1
    @test SymbolicUtils.is_caching_enabled(f1)
    SymbolicUtils.toggle_caching!(f1, false)
    @test !SymbolicUtils.is_caching_enabled(f1)
    f1(x)
    @test isempty(cache)
    @test stats.hits == stats.misses == stats.clears == 0
end

@cache function f2(x::Union{BasicSymbolic, UInt})::Union{BasicSymbolic, UInt}
    return 2x + 1
end

@testset "::Union (with `UInt`)" begin
    @syms x
    val = f2(x)
    @test isequal(val, 2x + 1)
    cachestruct = associated_cache(f2)
    cache, stats = cachestruct.tlv[]
    @test cache isa Dict{Tuple{Union{SymbolicKey, UInt}}, Union{BasicSymbolic, UInt}}
    @test length(cache) == 1
    @test cache[(SymbolicKey(objectid(x)),)] === val
    @test stats.hits == 0
    @test stats.misses == 1
    f2(x)
    @test stats.hits == 1
    @test stats.misses == 1

    y = objectid(x)
    val = f2(y)
    @test val == 2y + 1
    @test length(cache) == 2
    @test cache[(y,)] == val
    @test stats.misses == 2

    clear_cache!(f2)
    @test length(cache) == 0
    @test stats.hits == stats.misses == stats.clears == 0
end

@cache function f3(x)::Union{BasicSymbolic, Int}
    return 2x + 1
end

@cache function f3_2(x::Any)::Union{BasicSymbolic, Int}
    return 2x + 1
end

@testset "$name" for (name, fn) in [("implicit ::Any", f3), ("explicit ::Any", f3_2)]
    @syms x
    val = fn(x)
    @test isequal(val, 2x + 1)
    cachestruct = associated_cache(fn)
    cache, stats = cachestruct.tlv[]
    @test cache isa Dict{Tuple{Any}, Union{BasicSymbolic, Int}}
    @test length(cache) == 1
    @test cache[(SymbolicKey(objectid(x)),)] === val
    @test stats.hits == 0
    @test stats.misses == 1
    fn(x)
    @test stats.hits == 1
    @test stats.misses == 1

    val = fn(3)
    @test val == 7
    @test length(cache) == 2
    @test stats.misses == 2

    clear_cache!(fn)
    @test length(cache) == 0
    @test stats.hits == stats.misses == stats.clears == 0
end

@cache function f4(x::Union{BasicSymbolic, Int})::Union{BasicSymbolic, Int}
    x isa Number && return x
    if iscall(x)
        return maketerm(typeof(x), operation(x), map(f4, arguments(x)), metadata(x))
    end
    return f3(x)
end

@testset "Threading" begin
    @syms x y z
    @test isequal(f4(2x + 1), 2(2x + 1) + 1)

    function build_rand_expr(vars, depth, maxdepth)
        if depth < maxdepth
            v = build_rand_expr(vars, depth + 1, maxdepth)
        else
            v = rand(vars)
        end
        if isodd(depth)
            return v + rand([1:3; vars])
        else
            return v * rand([1:3; vars])
        end
    end

    exprs = [build_rand_expr([x, y, z], 0, 100) for _ in 1:1000]
    result = tmap(f4, exprs)
    truevals = map(f4, exprs)
    @test isequal(result, truevals)
end

@cache function f5(x::BasicSymbolic, y::Union{BasicSymbolic, Int}, z)::BasicSymbolic
    return x + y + z
end

# temporary defintion to induce objectid collisions
Base.objectid(x::BasicSymbolic) = 0x42

@testset "`objectid` collision handling" begin
    @syms x y z
    @test objectid(x) == objectid(y) == objectid(z) == 0x42
    cachestruct = associated_cache(f5)
    cache, stats = cachestruct.tlv[]
    val = f5(x, 1, 2)
    @test isequal(val, x + 3)
    @test length(cache) == 1
    @test stats.misses == 1
    val2 = f5(y, 1, 2)
    @test isequal(val2, y + 3)
    @test length(cache) == 1
    @test stats.misses == 2

    clear_cache!(f5)
    val = f5(x, y, z)
    @test isequal(val, x + y + z)
    @test length(cache) == 1
    @test stats.misses == 1
    val2 = f5(y, 2z, x)
    @test isequal(val2, x + y + 2z)
    @test length(cache) == 1
    @test stats.misses == 2
end

Base.delete_method(only(methods(objectid, @__MODULE__)))
@syms x
@test objectid(x) != 0x42
