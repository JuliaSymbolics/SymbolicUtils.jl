using Test
using MutableArithmetics
using SymbolicUtils

@syms x::Real y::Real
v = repeat([x, y], 10)
s = sum(v, init = 0)
@test s.dict[x] == 10
@test s.dict[y] == 10
@test isequal(s, 10x + 10y) # ????

a = x + y
b = 2x + y
c = add!!(a, b)
@test c.dict[x] == 3
@test c.dict[y] == 2
@test isequal(c, 3x + 2y)
