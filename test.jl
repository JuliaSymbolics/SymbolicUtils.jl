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

toexpr(optimized)
expr = A * B

is_array(x) = begin
    SU.symtype(x) <: AbstractArray
end
r = @rule ~a::is_array * ~b::is_array => LinearAlgebra.mul!(~b, ~a, ~b, 1, 1)
r = @rule ~a::is_array * ~b::is_array + ~c::is_array => LinearAlgebra.mul!(~c, ~a, ~b, 1, 1)
r = @rule ~~a::is_array * ~~b::is_array => ~~a
r = @rule ~~a::is_array * ~~b::is_array => ~~a
r = @rule ~a * ~b => ~a

r(expr)