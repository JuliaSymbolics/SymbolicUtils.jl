# SymbolicUtils.jl

SymbolicUtils.jl provides various utilities for symbolic computing.

## Examples

```julia
julia> using SymbolicUtils

julia> @vars a::Integer b c d x::Real y::Number
(a, b, c, d, x, y)

julia> simplify(a + b + (x * y) + c + 2 * (x * y) + d + sin(x)^2 + cos(x)^2 - y^0)
((3 * x * y) + a + b + c + d)
```