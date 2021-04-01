# This file was generated, do not modify it. # hide
using SymbolicUtils
using SymbolicUtils.Rewriters

sqexpand = @rule (~x + ~y)^2 => (~x)^2 + (~y)^2 + 2 * ~x * ~y
acpyid = @acrule sin(~x)^2 + cos(~x)^2 => 1

csa = Chain([sqexpand, acpyid])

csa((cos(x) + sin(x))^2)