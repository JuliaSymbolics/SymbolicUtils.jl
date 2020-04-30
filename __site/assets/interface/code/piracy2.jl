# This file was generated, do not modify it. # hide
using SymbolicUtils
using SymbolicUtils: Sym, Term, istree, operation, arguments, to_symbolic

SymbolicUtils.istree(ex::Expr) = ex.head == :call
SymbolicUtils.operation(ex::Expr) = ex.args[1]
SymbolicUtils.arguments(ex::Expr) = ex.args[2:end]
SymbolicUtils.to_symbolic(s::Symbol) = Sym(s)

@show simplify(ex)

dump(simplify(ex))