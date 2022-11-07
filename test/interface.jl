using SymbolicUtils, Test
using TermInterface

TermInterface.issym(s::Symbol) = true
Base.nameof(s::Symbol) = s

for f ∈ [:+, :-, :*, :/, :^]
    @eval begin
        Base.$f(x::Union{Expr, Symbol}, y::Number) = Expr(:call, $(nameof(f)), x, y)
        Base.$f(x::Number, y::Union{Expr, Symbol}) = Expr(:call, $(nameof(f)), x, y)
        Base.$f(x::Union{Expr, Symbol}, y::Union{Expr, Symbol}) = (Expr(:call, $(nameof(f)), x, y))
    end
end

Base.zero(t::Expr) = 0
TermInterface.symtype(::Expr) = Real
TermInterface.symtype(::Symbol) = Real

ex = 1 + (:x - 2)

# FIXME why is a simple expression broken, but complex is not? Reminds of PolyForm repr breakage
@test_broken simplify(ex) == -1 + :x
@test simplify(:a * (:b + -1 * :c) + -1 * (:b * :a + -1 * :c * :a), expand=true) == 0
