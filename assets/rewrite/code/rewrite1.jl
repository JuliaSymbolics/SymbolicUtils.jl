# This file was generated, do not modify it. # hide
using SymbolicUtils

@syms w z α::Real β::Real

(w, z, α, β) # hide

r1 = @rule ~x + ~x => 2 * (~x)

r1(sin(1+z) + sin(1+z))