# This file was generated, do not modify it. # hide
to_expr(t::Term) = Expr(:call, operation(t), to_expr.(arguments(t))...) 
to_expr(x) = x

@show expr = to_expr(simplify(ex))

dump(expr)