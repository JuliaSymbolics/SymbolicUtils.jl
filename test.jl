using SymbolicUtils
using SymbolicUtils.Code
import SymbolicUtils as SU
using Symbolics
using LinearAlgebra

# Create symbolic arrays for testing
@syms A[1:3, 1:3] B[1:3, 1:3] C[1:3, 1:3] D[1:3, 1:3]

expr = A * B + C
# optimized = apply_optimization(expr)
optimized = SU.Code.cse(expr)

build_function(optimized, [A, B, C]; array = true, cse = true)
build_function(expr, [A, B, C]; array = true, cse = true)
build_function(expr, [A, B, C]; array = true, cse = false)

toexpr(optimized)

SU.simplify(expr)
expr = A * B

is_array(x) = begin
    SU.symtype(x) <: AbstractArray
end
r = @rule ~a::is_array * ~b::is_array => LinearAlgebra.mul!(~b, ~a, ~b, 1, 1)
r = @rule ~a::is_array * ~b::is_array + ~c::is_array => begin
    tmp = copy(~c)
    LinearAlgebra.mul!(tmp, ~a, ~b, 1, 1)
end
r = @rule ~~a::is_array * ~~b::is_array => ~~a
r = @rule ~~a::is_array * ~~b::is_array => ~~a
r = @rule ~a * ~b => ~a

@register_array_symbolic LinearAlgebra.mul!(x::AbstractArray, y::AbstractArray, z::AbstractArray, α, β) begin
    size = size(x)
    eltype = eltype(x)
end
@register_symbolic Base.copy(x)
@register_array_symbolic Base.copy(x::AbstractArray) begin
    size = size(x)
    eltype = eltype(x)
end

r(expr)


toexpr(expr)
