# This file was generated, do not modify it. # hide
using SymbolicUtils

SymbolicUtils.istree(ex::Expr) = ex.head == :call
SymbolicUtils.operation(ex::Expr) = ex.args[1]
SymbolicUtils.arguments(ex::Expr) = ex.args[2:end]

@rule(~x => ~x - 1)(ex)