using BenchmarkTools, SymbolicUtils
using SymbolicUtils: is_literal_number, @rule
using Metatheory

using Random

SUITE = BenchmarkGroup()

@syms a b c d; Random.seed!(123);

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
    pform["isone"] = @benchmarkable SymbolicUtils.fraction_isone($o)
    pform["easy_iszero"] = @benchmarkable SymbolicUtils.fraction_iszero($((b*(h + (-e*g) / d)) / b + (e*g) / d - h))
end
