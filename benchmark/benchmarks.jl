using BenchmarkTools, SymbolicUtils
using SymbolicUtils: is_literal_number, @rule, ArrayMaker, IRStructure, populate_ir!, BasicSymbolic

using Random

SUITE = BenchmarkGroup()
SUITE["printing"] = BenchmarkGroup()

@syms a b c d x y[1:3] z[1:2, 1:2]; Random.seed!(123);

_make_bench_ir(expr::BasicSymbolic{T}) where {T} =
    (ir = IRStructure{T}(); populate_ir!(ir, expr); ir)

_symtype_param(::BasicSymbolic{T}) where {T} = T

@syms _poly_x::Real _poly_y::Real _poly_z::Real _poly_w::Real
@syms _wide_xs[1:100]::Real _wide_ys[1:100]::Real
@syms _ma_xs[1:400]::Real _ma_ys[1:400]::Real _ma_zs[1:400]::Real

function make_bench_makearray(n::Int; seed::Int = 42)
    T   = _symtype_param(_ma_xs[1])
    rng = Random.MersenneTwister(seed)

    n_regions = clamp(
        n ÷ 5 + round(Int, randn(rng) * sqrt(n / 5)),
        4, n ÷ 2
    )

    split_pts = sort(Random.shuffle!(rng, collect(2:n))[1:n_regions - 1])
    starts    = [1; split_pts]
    stops     = [split_pts .- 1; n]
    regions   = [(starts[i]:stops[i],) for i in 1:n_regions]

    values = map(1:n_regions) do i
        start, stop = starts[i], stops[i]
        len = stop - start + 1
        if len == 1
            return [_ma_xs[mod1(start, 10)] + _ma_ys[mod1(start, 10)]]
        end
        choice = rand(rng, 1:3)
        if choice == 1
            return @arrayop (k,) _ma_xs[k] * _ma_ys[k] k in 1:len
        elseif choice == 2
            return [iseven(k) ? _ma_xs[mod1(k, 10)] : _ma_ys[mod1(k, 10)] for k in 1:len]
        else
            sub_v1 = [_ma_zs[1] + _ma_xs[1]]
            sub_v2 = @arrayop (k,) _ma_ys[k] k in 1:(len - 1)
            return ArrayMaker{T}([(1:1,), (2:len,)], (sub_v1, sub_v2))
        end
    end

    return ArrayMaker{T}(regions, values)
end

function random_term(len; atoms, funs, fallback_atom=1)
    xs = rand(atoms, len)
    while length(xs) > 1
        xs = map(Iterators.partition(xs, 2)) do xy
            x = xy[1]; y = get(xy, 2, fallback_atom)
            rand(funs)(x, y)
        end
    end
    xs[]
end

let r = @rule(~x => ~x), rs = RuleSet([r]),
    acr = @rule(~x::is_literal_number + ~y => ~y)

    overhead = SUITE["overhead"]  = BenchmarkGroup()
    overhead["rule"]  = BenchmarkGroup()

    overhead["rule"]["noop:Int"]  = @benchmarkable $r(1)
    overhead["rule"]["noop:Sym"]  = @benchmarkable $r($a)
    overhead["rule"]["noop:Term"] = @benchmarkable $r($(a+2))

    overhead["acrule"]  = BenchmarkGroup()
    overhead["acrule"]["noop:Int"]  = @benchmarkable $acr(1)
    overhead["acrule"]["noop:Sym"]  = @benchmarkable $acr($a)
    overhead["acrule"]["a+2"] = @benchmarkable $acr($(a+2))
    overhead["acrule"]["a+b"] = @benchmarkable $acr($(a+b))
    overhead["acrule"]["a+2+b"] = @benchmarkable $acr($(a+2+b))

    overhead["ruleset"]  = BenchmarkGroup()
    overhead["ruleset"]["noop:Int"]  = @benchmarkable $rs(1)
    overhead["ruleset"]["noop:Sym"]  = @benchmarkable $rs($a)
    overhead["ruleset"]["noop:Term"] = @benchmarkable $rs($(a+2))

    overhead["simplify"]  = BenchmarkGroup()
    overhead["simplify"]["noop:Int"]  = @benchmarkable simplify(1)
    overhead["simplify"]["noop:Sym"]  = @benchmarkable simplify($a)
    overhead["simplify"]["noop:Term"] = @benchmarkable simplify($(a+2))

    ex1 = random_term(1000, atoms=[a, b, c, d, a^(-1), b^(-1), 1, 2.0], funs=[+, *])
    ex2 = random_term(1000, atoms=[a, b, c, d, a^(-1), b^(-1), 1, 2.0], funs=[/, *])

    overhead["simplify"]["randterm (+, *):serial"] = @benchmarkable simplify($ex1, simplify_fractions=false, threaded=false)
    overhead["simplify"]["randterm (/, *):serial"] = @benchmarkable simplify($ex2, simplify_fractions=false, threaded=false)
    overhead["simplify"]["randterm (+, *):thread"] = @benchmarkable simplify($ex1, simplify_fractions=false, threaded=true)
    overhead["simplify"]["randterm (/, *):thread"] = @benchmarkable simplify($ex2, simplify_fractions=false, threaded=true)

    overhead["substitute"] = BenchmarkGroup()


    # we use `fold = false` since otherwise it dynamic dispatches to `sin`/`cos` whenever
    # both arguments in the contained addition are substituted.

    overhead["substitute"]["a"] = @benchmarkable substitute(subs_expr, $(Dict(a=>1))) setup=begin
        subs_expr = (sin(a+b) + cos(b+c)) * (sin(b+c) + cos(c+a)) * (sin(c+a) + cos(a+b))
    end

    overhead["substitute"]["a,b"] = @benchmarkable substitute(subs_expr, $(Dict(a=>1, b=>2))) setup=begin
        subs_expr = (sin(a+b) + cos(b+c)) * (sin(b+c) + cos(c+a)) * (sin(c+a) + cos(a+b))
    end

    overhead["substitute"]["a,b,c"] = @benchmarkable substitute(subs_expr, $(Dict(a=>1, b=>2, c=>3))) setup=begin
        subs_expr = (sin(a+b) + cos(b+c)) * (sin(b+c) + cos(c+a)) * (sin(c+a) + cos(a+b))
    end

    overhead["get_degrees"] = BenchmarkGroup()

    let y1 = term(getindex, y, 1, type=Number),
        y2 = term(getindex, y, 2, type=Number),
        y3 = term(getindex, y, 3, type=Number),
        z11 = term(getindex, z, 1, 1, type=Number),
        z12 = term(getindex, z, 1, 2, type=Number),
        z23 = term(getindex, z, 2, 3, type=Number)

        # create a relatively large polynomial
        large_poly = SymbolicUtils.expand((x^2 + 2y1 + 3z12 + y2*z23 + x*y1*z12 - x^2*z12 + x*z11 + y3 + y2 + z23 + 1)^8)
        overhead["get_degrees"]["large_poly"] = @benchmarkable SymbolicUtils.get_degrees($large_poly)
        SUITE["printing"]["large_poly"] = @benchmarkable show(devnull, $large_poly)
    end
end

let
    pform = SUITE["polyform"]  = BenchmarkGroup()
    @syms a b c d e f g h i
    ex = (f + ((((g*(c^2)*(e^2)) / d - e*h*(c^2)) / b + (-c*e*f*g) / d + c*e*i) /
              (i + ((c*e*g) / d - c*h) / b + (-f*g) / d) - c*e) / b +
         ((g*(f^2)) / d + ((-c*e*f*g) / d + c*f*h) / b - f*i) /
         (i + ((c*e*g) / d - c*h) / b + (-f*g) / d)) / d

    o = (d + (e*((c*(g + (-d*g) / d)) / (i + (-c*(h + (-e*g) / d)) / b + (-f*g) / d))) / b +
         (-f*(g + (-d*g) / d)) / (i + (-c*(h + (-e*g) / d)) / b + (-f*g) / d)) / d
    pform["simplify_fractions"] = @benchmarkable simplify_fractions($ex)
    pform["iszero"] = @benchmarkable SymbolicUtils.fraction_iszero($ex)
    pform["isone"] = @benchmarkable SymbolicUtils.fraction_isone($ex)
    pform["isone:noop"] = @benchmarkable SymbolicUtils.fraction_isone($o)
    pform["iszero:noop"] = @benchmarkable SymbolicUtils.fraction_iszero($o)
    pform["easy_iszero"] = @benchmarkable SymbolicUtils.fraction_iszero($((b*(h + (-e*g) / d)) / b + (e*g) / d - h))
end

let
    arith = SUITE["arithmetic"] = BenchmarkGroup()
    atoms = [a, b, c, d, a^2, b^2, a^1.5, (b + c), b^c, 1, 2.0]
    funs = [+, *]
    exs = [random_term(5; atoms, funs) for _ in 1:50]
    @static if isdefined(SymbolicUtils, :SymReal)
        arith["addition"] = @benchmarkable SymbolicUtils.add_worker(SymReal, $exs)
    elseif isdefined(SymbolicUtils, :add_worker)
        arith["addition"] = @benchmarkable SymbolicUtils.add_worker($exs)
    else
        exs = Tuple(exs)
        arith["addition"] = @benchmarkable +($(exs)...)
    end

    funs = [*, /]
    exs = [random_term(5; atoms, funs) for _ in 1:50]
    @static if isdefined(SymbolicUtils, :SymReal)
        arith["2-arg mul"] = @benchmarkable SymbolicUtils.mul_worker(SymReal, $((exs[1], exs[2])))
        arith["multiplication"] = @benchmarkable SymbolicUtils.mul_worker(SymReal, $exs)
    elseif isdefined(SymbolicUtils, :mul_worker)
        arith["2-arg mul"] = @benchmarkable SymbolicUtils.mul_worker($((exs[1], exs[2])))
        arith["multiplication"] = @benchmarkable SymbolicUtils.mul_worker($exs)
    else
        exs = Tuple(exs)
        arith["2-arg mul"] = @benchmarkable *($(exs[1]), $(exs[2]))
        arith["multiplication"] = @benchmarkable *($(exs)...)
    end

    ex1 = random_term(50; atoms, funs)
    ex2 = random_term(50; atoms, funs)
    arith["division"] = @benchmarkable $ex1 / $ex2
end

@static if length(methods(SymbolicUtils.clear_cache!)) < 4
    SymbolicUtils.clear_cache!(sub::SymbolicUtils.IRSubstituter) = empty!(sub.cache)
end

function bench_sub(subber, ex)
    SymbolicUtils.clear_cache!(subber)
    subber(ex)
end

let
    atoms = atoms = [a, b, c, d, a^2, b^2, a^1.5, (b + c), b^c, 1, 2.0]
    funs = [+, *, hypot, (x, y) -> abs(x), (x, y) -> exp(x)]
    ex = random_term(100000; atoms, funs)
    rules = Dict(a => 2sin(b))
    SUITE["irstructure"] = BenchmarkGroup()
    SUITE["irstructure"]["substitute"] = BenchmarkGroup()

    subber = SymbolicUtils.Substituter{false}(rules)
    SUITE["irstructure"]["substitute"]["reference"] = @benchmarkable bench_sub($subber, $ex)
    ir = IRStructure{SymReal}()
    subber = SymbolicUtils.IRSubstituter{false}(ir, rules)
    SUITE["irstructure"]["substitute"]["IRSubstituter"] = @benchmarkable bench_sub($subber, $ex)

    # To benchmark a much more sparse substitution
    rules = Dict(abs(b + c) => 2sin(b))
    subber = SymbolicUtils.Substituter{false}(rules)
    SUITE["irstructure"]["substitute"]["sparse reference"] = @benchmarkable bench_sub($subber, $ex)
    ir = IRStructure{SymReal}()
    subber = SymbolicUtils.IRSubstituter{false}(ir, rules)
    SUITE["irstructure"]["substitute"]["sparse IRSubstituter"] = @benchmarkable bench_sub($subber, $ex)
end

let
    codegen = SUITE["codegen"] = BenchmarkGroup()

    codegen["wide_poly"] = BenchmarkGroup()
    for n_terms in (25, 50, 100)
        expr     = sum(_wide_xs[i] * _wide_ys[i] for i in 1:n_terms)
        cse_expr = SymbolicUtils.Code.cse(expr)
        ir       = _make_bench_ir(expr)
        codegen["wide_poly"]["n=$n_terms:toexpr"]      = @benchmarkable SymbolicUtils.Code.toexpr($cse_expr)
        codegen["wide_poly"]["n=$n_terms:fast_toexpr"] = @benchmarkable SymbolicUtils.Code.fast_toexpr($expr, $ir, Dict{Any,Any}())
    end

    codegen["deep_poly"] = BenchmarkGroup()
    for deg in (6, 10, 14)
        expr     = SymbolicUtils.expand((_poly_x + _poly_y + _poly_z)^deg)
        cse_expr = SymbolicUtils.Code.cse(expr)
        ir       = _make_bench_ir(expr)
        codegen["deep_poly"]["deg=$deg:toexpr"]      = @benchmarkable SymbolicUtils.Code.toexpr($cse_expr)
        codegen["deep_poly"]["deg=$deg:fast_toexpr"] = @benchmarkable SymbolicUtils.Code.fast_toexpr($expr, $ir, Dict{Any,Any}())
    end

    let
        expr     = SymbolicUtils.expand((_poly_x + _poly_y + _poly_z + _poly_w)^12)
        cse_expr = SymbolicUtils.Code.cse(expr)
        ir       = _make_bench_ir(expr)
        codegen["wide_deep_poly"] = BenchmarkGroup()
        codegen["wide_deep_poly"]["toexpr"]      = @benchmarkable SymbolicUtils.Code.toexpr($cse_expr)
        codegen["wide_deep_poly"]["fast_toexpr"] = @benchmarkable SymbolicUtils.Code.fast_toexpr($expr, $ir, Dict{Any,Any}())
    end

    codegen["makearray"] = BenchmarkGroup()
    for n in (100, 200, 400)
        expr     = make_bench_makearray(n)
        cse_expr = SymbolicUtils.Code.cse(expr)
        ir       = _make_bench_ir(expr)
        codegen["makearray"]["n=$n:toexpr"]      = @benchmarkable SymbolicUtils.Code.toexpr($cse_expr)
        codegen["makearray"]["n=$n:fast_toexpr"] = @benchmarkable SymbolicUtils.Code.fast_toexpr($expr, $ir, Dict{Any,Any}())
    end

    let
        @syms _ao_A[1:8, 1:8, 1:8]::Real _ao_B[1:8, 1:8, 1:8]::Real
        expr     = @arrayop (i, j) _ao_A[i, k, l] * _ao_B[j, k, l]
        cse_expr = SymbolicUtils.Code.cse(expr)
        ir       = _make_bench_ir(expr)
        codegen["arrayop_nested"] = BenchmarkGroup()
        codegen["arrayop_nested"]["toexpr"]      = @benchmarkable SymbolicUtils.Code.toexpr($cse_expr)
        codegen["arrayop_nested"]["fast_toexpr"] = @benchmarkable SymbolicUtils.Code.fast_toexpr($expr, $ir, Dict{Any,Any}())
    end
end
