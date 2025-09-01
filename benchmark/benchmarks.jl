using BenchmarkTools, SymbolicUtils
using SymbolicUtils: is_literal_number, @rule

using Random

SUITE = BenchmarkGroup()

@syms a b c d x y[1:3] z[1:2, 1:2]; Random.seed!(123);

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
        arith["multiplication"] = @benchmarkable SymbolicUtils.mul_worker(SymReal, $exs)
    elseif isdefined(SymbolicUtils, :mul_worker)
        arith["multiplication"] = @benchmarkable SymbolicUtils.mul_worker($exs)
    else
        exs = Tuple(exs)
        arith["multiplication"] = @benchmarkable *($(exs)...)
    end

    ex1 = random_term(50; atoms, funs)
    ex2 = random_term(50; atoms, funs)
    arith["division"] = @benchmarkable $ex1 / $ex2
end
