# This file was generated, do not modify it. # hide
using SymbolicUtils

@syms w z α::Real β::Real

(w, z, α, β) # hide

r1 = @rule sin(2(~x)) => 2sin(~x)*cos(~x)

r1(sin(2z))