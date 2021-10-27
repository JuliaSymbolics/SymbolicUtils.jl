using SymbolicUtils

sym_eq(x, y) = simplify(x == y)
(≖)(x, y) = sym_eq(x,y)

@syms a b
ex = 2a + 2b - (a*(a + b))
res = optimize(ex)
@test res ≖ (a+b)*(2-a)


# TODO test metadata
ex = sin(a^2)/cos(a^2)
res = optimize(ex)
@test isequal(res, tan(a^2)) # sym_eq does not work