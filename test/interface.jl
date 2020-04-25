
using SymbolicUtils: Term, to_symbolic
SymbolicUtils.symtype(::Union{Expr, Symbol}) = Number
SymbolicUtils.istree(ex::Expr) = ex.head == :call
SymbolicUtils.operation(ex::Expr) = ex.args[1]
SymbolicUtils.arguments(ex::Expr) = ex.args[2:end]

for f ∈ [:+, :-, :*, :/, :^]
    @eval begin
        Base.$f(x::Union{Expr, Symbol}, y::Number) = Expr(:call, $f, x, y) |> to_symbolic
        Base.$f(x::Number, y::Union{Expr, Symbol}) = Expr(:call, $f, x, y) |> to_symbolic
        Base.$f(x::Union{Expr, Symbol}, y::Union{Expr, Symbol}) = (Expr(:call, $f, x, y)) |> to_symbolic
    end
end
SymbolicUtils.nameof(f::Symbol) = f


ex = 1 + (:x - 2)

@test to_symbolic(ex) == Term{Number}(+, [1, Term{Number}(-, [:x, 2])])
@test simplify(ex) == -1 + :x

