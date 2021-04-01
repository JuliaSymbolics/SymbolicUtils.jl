# This file was generated, do not modify it. # hide
using SymbolicUtils.Rewriters: RestartedChain

rcas = RestartedChain([acpyid, sqexpand])

rcas((cos(x) + sin(x))^2)