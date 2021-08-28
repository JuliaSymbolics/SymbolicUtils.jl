## Term representation and simplification

Performance of symbolic simplification depends on the datastructures used to represent terms. Efficient datastructures often have the advantage of automatic simplification, and of efficient storage.

The most basic term representation simply holds a function call and stores the function and the arguments it is called with. This is done by the `Term` type in SymbolicUtils. Functions that aren't commutative or associative, such as `sin` or `hypot` are stored as `Term`s. Commutatative and associative operations like `+`, `*`, and their supporting operations like `-`, `/` and `^`, when used on terms of type `<:Number`, stand to gain from the use of more efficient datastrucutres.

All term representations must support `operation` and `arguments` functions. And they must define `istree` to return `true` when called with an instance of the type. Generic term-manipulation programs such as the rule-based rewriter make use of this interface to inspect expressions. In this way, the interface wins back the generality lost by having a zoo of term representations instead of one. (see [interface](/interface/) section for more on this.)


### Preliminary representation of arithmetic

Linear combinations such as $\alpha_1  x_1 + \alpha_2 x_2 +...+ \alpha_n x_n$ are represented by `Add(Dict(x₁ => α₁, x₂ => α₂, ..., xₙ => αₙ))`. Here, any $x_i$ may itself be other types mentioned here, except for `Add`. When an `Add` is added to an `Add`, we merge their dictionaries and add up matching coefficients to create a single "flattened" Add.

Similarly, $x_1^{m_1}x_2^{m_2}...x_{m_n}$ is represented by
`Mul(Dict(x₁ => m₁, x₂ => m₂, ..., xₙ => mₙ))`. $x_i$ may not themselves be `Mul`, multiplying a Mul with another Mul returns a "flattened" Mul.

Note that `Add` and `Mul` types perform a preliminary simplification which suffices to simplify numeric expressions to a large extent during construction.

$p / q$ is represented by `Div(p, q)`. The result of `*` on `Div` is maintainted as a `Div`. For example, `Div(p_1, q_1) * Div(p_2, q_2)` results in `Div(p_1 * p_2, q_1 * q_2)` and so on. The effect is, in `Div(p, q)`, `p` or `q` or, if they are Mul, any of their multiplicands is not a Div. So `Mul`s must always be nested inside a `Div` and can never show up immediately wrapping it. This rule sets up an expression so that it helps the `simplify_fractions` procedure described two sections below.


### Polynomial representation

Packages like DynamicPolynomials.jl provide representations that are even more efficient than the `Add` and `Mul` types mentioned above. They are designed specifically for multi-variate polynomials. They provide common algorithms such as multi-variate polynomial GCD. The restrictions that make it fast also mean some things are not possible: Firstly, DynamicPolynomials can only represent flat polynomials. For example, `(x-3)*(x+5)` can only be represented as `(x^2) + 15 - 8x`. Secondly, DynamicPolynomials does not have ways to represent generic Terms such as `sin(x-y)` in the tree.

To reconcile these differences while being able to use the efficient algorithms of DynamicPolynomials we have the `PolyForm` type. This type holds a polynomial and the mappings necessary to present the polynomial as a SymbolicUtils expression (i.e. by defining `operation` and `arguments`).  The mappings constructed for the conversion are 1) a bijection from DynamicPolynomials PolyVar type to a Symbolics `Sym`, and 2) a mapping from `Sym`s to non-polynomial terms that the `Sym`s stand-in for. These terms may themselves contain PolyForm if there are polynomials inside them. The mappings are transiently global, that is, when all references to the mappings go out of scope, they are released and re-created.

```julia
julia> @syms x y
(x, y)

julia> PolyForm((x-3)*(y-5))
x*y + 15 - 5x - 3y
```

Terms for which the `operation` is not `+`, `*`, or `^` are replaced with a generated symbol when representing the polynomial, and a mapping from this new symbol to the original expression it stands-in for is maintained as stated above.

```julia
julia> p = PolyForm((sin(x) + cos(x))^2)
(cos(x)^2) + 2cos(x)*sin(x) + (sin(x)^2)

julia> p.p # this is the actual DynamicPolynomial stored
cos_3658410937268741549² + 2cos_3658410937268741549sin_10720964503106793468 + sin_10720964503106793468²
```

By default, polynomials inside non-polynomial terms are not also converted to PolyForm. For example,

```julia
julia> PolyForm(sin((x-3)*(y-5)))
sin((x - 3)*(y - 5))
```
But you can pass in the `recurse=true` keyword argument to do this.

```julia
julia> PolyForm(sin((x-3)*(y-5)), recurse=true)
sin(x*y + 15 - 5x - 3y)
```

Polynomials are constructed by first turning symbols and non-polynomial terms into DynamicPolynomials-style variables and then applying the `+`, `*`, `^` operations on these variables. You can control the list of the polynomial operations with the `Fs` keyword argument. It is a `Union` type of the functions to apply. For example, let's say you want to turn terms into polynomials by only applying the `+` and `^` operations, and want to preserve `*` operations as-is, you could pass in `Fs=Union{typeof(+), typeof(^)}`

```julia
julia> PolyForm((x+y)^2*(x-y), Fs=Union{typeof(+), typeof(^)}, recurse=true)
((x - (y))*((x^2) + 2x*y + (y^2)))
```

Note that in this case `recurse=true` was necessary as otherwise the polynomialization would not descend into the `*` operation as it is now considered a generic operation.

### Simplifying fractions

`simplify_fractions(expr)` recurses through `expr` finding `Div`s and simplifying them using polynomial divison.

First the factors of the numerators and the denominators are converted into PolyForm objects, then numerators and denominators are divided by their respective pairwise GCDs. The conversion of the numerator and denominator into PolyForm is set up so that `simplify_fractions` does not result in increase in the expression size due to polynomial expansion. Specifically, the factors are individually converted into PolyForm objects, and any powers of polynomial is not expanded, but the divison process repeatedly divides them as many times as the power.


```julia
julia> simplify_fractions((x*y+5x+3y+15)/((x+3)*(x-4)))
(5.0 + y) / (x - 4)

julia> simplify_fractions((x*y+5x+3y+15)^2/((x+3)*(x-4)))
((5.0 + y)*(15 + 5x + x*y + 3y)) / (x - 4)

julia> simplify_fractions(3/(x+3) + x/(x+3))
1

julia> simplify_fractions(sin(x)/cos(x) + cos(x)/sin(x))
(cos(x)^2 + sin(x)^2) / (cos(x)*sin(x))

julia> simplify(ans)
1 / (cos(x)*sin(x))
```
