# SymbolicUtils.jl — Symbolic programming in Julia

## Features

- Fast expressions
- A [rule-based rewriting language](/rewrite/#rule-based_rewriting).
- A [combinator library](/rewrite/#composing_rewriters) for making rewriters.
- [Efficient representation](/representation/) of numeric expressions
- Type promotion:
  - Symbols (`Sym`s) carry type information. ([read more](#creating_symbolic_expressions))
  - Compound expressions composed of `Sym`s propagate type information. ([read more](#expression_interface))
- Set of extendable [simplification rules](#simplification).


## Creating symbolic expressions

First, let's use the `@syms` macro to create a few symbols.

```julia:syms1
using SymbolicUtils

@syms w z α::Real β::Real

(w, z, α, β) # hide

```

Type annotations are optional when creating symbols. Here `α`, `β` behave like Real numbers. `w` and `z` behave like `Number`, which is the default. You can use the `symtype` function to find the type of a symbol.

```julia:symtype
using SymbolicUtils: symtype

symtype(w), symtype(z),  symtype(α), symtype(β)
```

Note however that they are not subtypes of these types!

```julia:symtype2
@show w isa Number
@show α isa Real
```

As their types are different:

```julia:symtype3
@show typeof(w)
@show typeof(α)
```

(see [this post](https://discourse.julialang.org/t/ann-symbolicutils-jl-groundwork-for-a-symbolic-ecosystem-in-julia/38455/13?u=shashi) for why they are all not just subtypes of `Number`)

You can do basic arithmetic on symbols to get symbolic expressions:

```julia:expr
expr1 = α*sin(w)^2 + β*cos(z)^2
expr2 = α*cos(z)^2 + β*sin(w)^2

expr1 + expr2
```

SymbolicUtils automatically simplifies

```julia:creating1
2w + 3w - 3z + α
```

and reorders

```julia:creating2
(z + w)*(α + β)
```

expressions of type `Symbolic{<:Number}` (which includes `Sym{Real}`) when they are created. It also does constant elimination (including rational numbers)

```julia:creating3
5 + 2w - 3z + α - (β + 5//3) + 3w - 2 + 3//2 * β
```

It's worth remembering that the expression may be transformed with respect to the input when it's created.


## Function-like symbols

Symbols can be defined to behave like functions. Both the input and output types for the function can be specified. Any application to that function will only admit either values of those types or symbols of the same `symtype`.

```julia:syms2
using SymbolicUtils
@syms f(x) g(x::Real, y::Real)::Real

f(z) + g(1, α) + sin(w)
```

This does not work since `z` is a `Number`, not a `Real`.

```julia:sym3
g(1, z)
```

This works because `g` "returns" a `Real`.

```julia:sym4
g(2//5, g(1, β))
```



## Expression interface

Symbolic expressions are of type `Term{T}`, `Add{T}`, `Mul{T}`, `Pow{T}` or `Div{T}` and denote some function call where one or more arguments are themselves such expressions or `Sym`s. See more about the representation [here](/representation/).

All the expression types support the following:

- `istree(x)` -- always returns `true` denoting, `x` is not a leaf node like Sym or a literal.
- `operation(x)` -- the function being called
- `arguments(x)` -- a vector of arguments
- `symtype(x)` -- the "inferred" type (`T`)

See more on the interface [here](/interface)


## Term rewriting

SymbolicUtils contains [a rule-based rewriting language](/rewrite/#rule-based_rewriting) for easy pattern matching and rewriting of expression. There is also a [combinator library](/rewrite/#composing_rewriters) to combine rules to chain, branch and loop over rules.

## Simplification

By default `+`, `*` and `^` operations apply the most basic simplification upon construction of the expression.

The rules with which the canonical form of `Symbolic{<:Number}` terms are constructed are the next (where `x isa Symbolic` and `c isa Number`)

 -  `0 + x`, `1 * x` and `x^1` always gives `x`
 -  `0 * x` always gives `0` and `x ^ 0` gives `1`
 -  `-x` becomes `(-1)*x`
 -  commutativity and associativity over `+` and `*` are assumed. Re-ordering of terms will be done under a [total order](https://github.com/JuliaSymbolics/SymbolicUtils.jl/blob/master/src/ordering.jl)
 - `p/q * x` or `x * p/q` results in `(p*x)/q`
 - `p/q * x/y` results in `(p*x)/(q*y)`
 -  `x + ... + x` will be fused into `n*x` with type `Mul`
 -  `x * ... * x` will be fused into `x^n` with type `Pow`
 -  sum of `Add`'s are fused
 -  product of `Mul`'s are fused
 -  `c * (c₁x₁ + ... + cₙxₙ)` will be converted into `c*c₁*x₁ + ... + c*cₙ*xₙ`
 -  `(x₁^c₁ * ... * xₙ^cₙ)^c` will be converted into `x₁^(c*c₁) * ... * xₙ^(c*cₙ)`
 -  there are come other simplifications on construction that you can check [here](https://github.com/JuliaSymbolics/SymbolicUtils.jl/blob/master/src/methods.jl)


Here is an example of this

```julia:simplify1
2 * (w+w+α+β + sin(z)^2 + cos(z)^2 - 1)
```

The `simplify` function applies a built-in set of rules to rewrite expressions in order to simplify it.

```julia:simplify2
simplify(2 * (w+w+α+β + sin(z)^2 + cos(z)^2 - 1))
```

The rules in the default simplify applies simple constant elimination and trigonometric identities.

If you read the previous section on the rules DSL, you should be able to read and understand the [rules](https://github.com/JuliaSymbolics/SymbolicUtils.jl/blob/master/src/simplify_rules.jl) that are used by `simplify`.

## Code generation

**Experimental feature**

It is common to want to generate executable code from symbolic expressions and blocks of them. We are working on experimental support for turning Symbolic expressions into executable functions with specific focus on array input and output and performance which is critical to the Differential Equations ecosystem which is making heavy use of this package.

See [Code generation](/codegen/) for more about this.

## Learn more

If you have a package that you would like to utilize rule-based rewriting in, look at the suggestions in the [Interfacing](/interface/) section to find out how you can do that without any fundamental changes to your package. Look at the [API documentation](/api/) for docstrings about specific functions or macros.

Head over to the github repository to ask questions and [report problems](https://github.com/JuliaSymbolics/SymbolicUtils.jl)! Join the [Zulip stream](https://julialang.zulipchat.com/#narrow/stream/236639-symbolic-programming) to chat!

