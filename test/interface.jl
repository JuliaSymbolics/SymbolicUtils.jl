using SymbolicUtils, Test
using SymbolicUtils: Term, Sym, istree, operation, arguments, symtype

SymbolicUtils.istree(ex::Expr) = ex.head == :call
SymbolicUtils.operation(ex::Expr) = ex.args[1]
SymbolicUtils.arguments(ex::Expr) = ex.args[2:end]

for f ∈ [:+, :-, :*, :/, :^]
    @eval begin
        Base.$f(x::Union{Expr, Symbol}, y::Number) = Expr(:call, $f, x, y)
        Base.$f(x::Number, y::Union{Expr, Symbol}) = Expr(:call, $f, x, y)
        Base.$f(x::Union{Expr, Symbol}, y::Union{Expr, Symbol}) = (Expr(:call, $f, x, y))
    end
end

ex = 1 + (:x - 2)

@test simplify(ex) == ex # Not simplified because symtype Any

SymbolicUtils.symtype(::Expr) = Real

@test simplify(ex) == -1 + :x
@test simplify(:a * (:b + -1 * :c) + -1 * (:b * :a + -1 * :c * :a), polynorm=true) == 0
