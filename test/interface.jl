using SymbolicUtils, Test
using SymbolicUtils: Term, Sym, operation, arguments, symtype
using TermInterface

TermInterface.istree(ex::Expr) = ex.head == :call
TermInterface.operation(ex::Expr) = ex.args[1]
TermInterface.arguments(ex::Expr) = ex.args[2:end]
TermInterface.similarterm(x::Type{Expr}, head, args, symtype=nothing; metadata=nothing) = 
    Expr(:call, head, args...)

for f ∈ [:+, :-, :*, :/, :^]
    @eval begin
        Base.$f(x::Union{Expr, Symbol}, y::Number) = Expr(:call, $f, x, y)
        Base.$f(x::Number, y::Union{Expr, Symbol}) = Expr(:call, $f, x, y)
        Base.$f(x::Union{Expr, Symbol}, y::Union{Expr, Symbol}) = (Expr(:call, $f, x, y))
    end
end

Base.zero(t::Expr) = 0
TermInterface.symtype(::Expr) = Real
TermInterface.symtype(::Symbol) = Real

ex = 1 + (:x - 2)

@test simplify(ex) == -1 + :x
@test simplify(:a * (:b + -1 * :c) + -1 * (:b * :a + -1 * :c * :a), expand=true) == 0
