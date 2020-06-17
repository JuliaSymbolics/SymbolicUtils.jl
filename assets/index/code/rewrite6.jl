# This file was generated, do not modify it. # hide
using SymbolicUtils.Rewriters

r1 = @rule ~x + ~x => 2 * (~x)
r2 = @rule ~x * +(~~ys) => sum(map(y-> ~x * y, ~~ys));

rset = Postwalk(Chain([r1, r2]))
rset_result = rset(2 * (w+w+α+β))

showraw(rset_result)