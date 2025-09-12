"""
    trigexpand(expr)

Apply trigonometric product-to-sum expansion to the expression.
This is equivalent to calling `simplify(expr, trigexpand=true)`.

Converts products of trigonometric functions to their sum forms using the identities:
- `cos(A) * cos(B) = (cos(A-B) + cos(A+B)) / 2`
- `sin(A) * sin(B) = (cos(A-B) - cos(A+B)) / 2`
- `sin(A) * cos(B) = (sin(A+B) + sin(A-B)) / 2`
- `cos(A) * sin(B) = (sin(A+B) - sin(A-B)) / 2`

# Examples
```jldoctest
julia> @syms A B
(A, B)

julia> trigexpand(cos(A) * cos(B))
(1//2)*(cos(A - B) + cos(A + B))

julia> @syms t ω φ ψ
(t, ω, φ, ψ)

julia> trigexpand(cos(ω*t + φ) * cos(ω*t + φ - ψ))
(1//2)*(cos(ψ) + cos(2φ - ψ + 2t*ω))
```
"""
function trigexpand(expr)
    return simplify(expr, trigexpand=true)
end