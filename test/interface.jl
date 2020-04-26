using SymbolicUtils, Test
using SymbolicUtils: Term, to_symbolic, istree, operation, arguments

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

@test to_symbolic(ex) == Term{Any}(+, [1, Term{Any}(-, [:x, 2])])
@test simplify(ex) == to_symbolic(-1 + :x)

to_expr(t::Term) = Expr(:call, operation(t), to_expr.(arguments(t))...) 
to_expr(x) = x

to_expr(simplify(ex))
