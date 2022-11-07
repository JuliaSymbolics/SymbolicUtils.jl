using SymbolicUtils

ops = [*, +, -, /, ^]
syms = (@syms a b c d e f g h i j k l m n o p q r s t u v w x y z) |> collect
constant_vals = -10:0.3:10
function rand_expr(d=0, mindepth=70, maxdepth=100)
    if d < mindepth
        (rand(ops))(rand_expr(d+1, mindepth, maxdepth), rand_expr(d+1, mindepth, maxdepth))
    elseif d >= maxdepth
        rand(0:8) == 0 ? rand(constant_vals) : rand(syms)
    elseif mindepth <= d < maxdepth
        rand(Bool) ? (rand(0:2) == 0 ? rand(constant_vals) : rand(syms)) : term(rand(ops), rand_expr(d+1, mindepth, maxdepth), rand_expr(d+1, mindepth, maxdepth))
    end 
end

ex = rand_expr(0, 12, 12)

syms = (@syms a b c d e f g h i j k l m n o p q r s t u v w x y z) |> collect

optimized = optimize(ex)

ex_expr = SymbolicUtils.Code.toexpr(ex)
optimized_expr = SymbolicUtils.Code.toexpr(optimized)

ex_f = eval(:((a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z )-> $ex_expr))
optimized_f = eval(:((a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z )-> $optimized_expr))

vals = collect(1:26)

ex_f(vals...)
optimized_f(vals...)

@btime ex_f($vals...)
@btime optimized_f($vals...)

