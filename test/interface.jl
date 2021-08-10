using SymbolicUtils, Test
using SymbolicUtils: Term, Sym, gethead, getargs, symtype
using TermInterface

TermInterface.isterm(ex::Expr) = ex.head == :call
TermInterface.gethead(ex::Expr) = ex.args[1]
SymbolicUtils.getargs(ex::Expr) = ex.args[2:end]

for f ∈ [:+, :-, :*, :/, :^]
    @eval begin
        Base.$f(x::Union{Expr, Symbol}, y::Number) = Expr(:call, $f, x, y)
        Base.$f(x::Number, y::Union{Expr, Symbol}) = Expr(:call, $f, x, y)
        Base.$f(x::Union{Expr, Symbol}, y::Union{Expr, Symbol}) = (Expr(:call, $f, x, y))
    end
end

ex = 1 + (:x - 2)

@test simplify(ex) == ex

TermInterface.symtype(::Expr) = Real
TermInterface.symtype(::Symbol) = Real
@test simplify(ex) == -1 + :x
@test simplify(:a * (:b + -1 * :c) + -1 * (:b * :a + -1 * :c * :a), expand=true) == 0
