using SymbolicUtils, Test
using SymbolicUtils: Term, Variable, to_symbolic, istree, operation, arguments

SymbolicUtils.istree(ex::Expr) = ex.head == :call
SymbolicUtils.operation(ex::Expr) = ex.args[1]
SymbolicUtils.arguments(ex::Expr) = ex.args[2:end]
SymbolicUtils.to_symbolic(s::Symbol) = Variable(s)

for f ∈ [:+, :-, :*, :/, :^]
    @eval begin
        Base.$f(x::Union{Expr, Symbol}, y::Number) = Expr(:call, $f, x, y)
        Base.$f(x::Number, y::Union{Expr, Symbol}) = Expr(:call, $f, x, y)
        Base.$f(x::Union{Expr, Symbol}, y::Union{Expr, Symbol}) = (Expr(:call, $f, x, y))
    end
end

ex = 1 + (:x - 2)

@test to_symbolic(ex) == Term{Any}(+, [1, Term{Any}(-, [Variable{Any}(:x), 2])])
@test simplify(ex) == to_symbolic(-1 + :x)

to_expr(t::Term) = Expr(:call, operation(t), to_expr.(arguments(t))...) 
to_expr(s::Variable) = s.name
to_expr(x) = x

@test to_expr(simplify(ex)) == Expr(:call, +, -1, :x)

SymbolicUtils.symtype(::Symbol) = Number


