# This file was generated, do not modify it. # hide
using SymbolicUtils

@syms x::Real y::Real

sqexpand = @rule (~x + ~y)^2 => (~x)^2 + (~y)^2 + 2 * ~x * ~y

sqexpand((cos(x) + sin(x))^2)