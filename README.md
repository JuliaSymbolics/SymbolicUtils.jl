# SymbolicUtils.jl

SymbolicUtils.jl provides various utilities for symbolic computing.

[![Build Status](https://travis-ci.org/JuliaSymbolics/SymbolicUtils.jl.svg?branch=master)](https://travis-ci.org/JuliaSymbolics/SymbolicUtils.jl)  [![Coverage Status](https://coveralls.io/repos/github/JuliaSymbolics/SymbolicUtils.jl/badge.svg?branch=master)](https://coveralls.io/github/JuliaSymbolics/SymbolicUtils.jl?branch=master)

## Variables and expressions

Variables can be created using the `@vars` macro:

```julia
julia> using SymbolicUtils

julia> @vars a::Integer b c d x::Real y::Number
(a, b, c, d, x, y)
```

The types annotated are used by the rewrite rules for symbolic simplification. 

Arithmetic and math functions are defined on variables and return `Term` objects which represent bigger expressions.

Variables can be defined as callable:

```julia
julia> @vars f(x) g(x::Real, y::Real)::Real
(f(::Number)::Number, g(::Real, ::Real)::Real)

julia> f(c)
f(c)

julia> g(a, x)
g(a, x)
```

## Symbolic simplification

Use the `simplify` function to apply a built in list of rules to simplify an expression.
```julia

julia> simplify(a + b + (x * y) + c + 2 * (x * y) + d + sin(x)^2 + cos(x)^2 - y^0)
((3 * x * y) + a + b + c + d)
```

## Pattern matching and rewriting

Expression rewriting rules can be created using the `@rule` macro `@rule LHS => RHS`.

Creates a `Rule` object. A rule object is callable, and  takes an expression and rewrites
it if it matches the LHS pattern to the RHS pattern, returns `nothing` otherwise.
The rule language is described below.

LHS can be any possibly nested function call expression where any of the arugments can
optionally be a Slot (`~x`) or a Segment (`~~x`) (described below).

If an expression matches LHS entirely, then it is rewritten to the pattern in the RHS
Segment (`~x`) and slot variables (`~~x`) on the RHS will substitute the result of the
matches found for these variables in the LHS.

**Slot**:

A Slot variable is written as `~x` and matches a single expression. `x` is the name of the variable. If a slot appears more than once in an LHS expression then expression matched at every such location must be equal (as shown by `isequal`).

_Example:_

Simple rule to turn any `sin` into `cos`:

```julia
julia> @vars a b c
(a, b, c)

julia> r = @rule sin(~x) => cos(~x)
sin(~x) => cos(~x)

julia> r(sin(1+a))
cos((1 + a))
```

A rule with 2 segment variables

```julia
julia> r = @rule ~x - ~y => ~x + (-(~y))
~x - ~y => ~x + -(~y)

julia> r(a-2b)
(a + (-(2 * b)))
```

A rule that matches two of the same expressions:

```julia
julia> r = @rule sin(~x)^2 + cos(~x)^2 => 1
sin(~x) ^ 2 + cos(~x) ^ 2 => 1

julia> r(sin(2a)^2 + cos(2a)^2)
1

julia> r(sin(2a)^2 + cos(a)^2)
# nothing
```

**Segment**:

A Segment variable is written as `~~x` and matches zero or more expressions in the
function call.

_Example:_

This implements the distributive property of multiplication: `+(~~ys)` matches expressions
like `a + b`, `a+b+c` and so on. On the RHS `~~ys` presents as any old julia array.

```julia
julia> r = @rule ~x * +((~~ys)) => sum(map(y-> ~x * y, ~~ys));

julia> r(2 * (a+b+c))
((2 * a) + (2 * b) + (2 * c))
```

**Predicates**:

Predicates can be used on both `~x` and `~~x` by using the `~x::f` or `~~x::f`.
Here `f` can be any julia function. In the case of a slot the function gets a single
matched subexpression, in the case of segment, it gets an array of matched expressions.

The predicate should return `true` if the current match is acceptable, and `false`
otherwise.

```julia
julia> two_πs(x::Number) = abs(round(x/(2π)) - x/(2π)) < 10^-9
two_πs (generic function with 1 method)

julia> two_πs(x) = false
two_πs (generic function with 2 methods)

julia> r = @rule sin(~~x + ~y::two_πs + ~~z) => sin(+(~~x..., ~~z...))
sin(~(~x) + ~(y::two_πs) + ~(~z)) => sin(+(~(~x)..., ~(~z)...))

julia> r(sin(a+3π))

julia> r(sin(a+6π))
sin(a)

julia> r(sin(a+6π+c))
sin((a + c))
```

The predicate function gets an array of values if attached to a segment variable (`~~x`).

### Associative-Commutative Rules
Given an expression `f(x, f(y, z, u), v, w)`, a `f` is said to be associative if the expression
is equivalent to `f(x, y, z, u, v, w)` and commutative if the order of arguments does not matter.
SymbolicUtils has a special `@acrule` macro meant for rules on functions which are associate 
and commutative such as addition and multiplication of real and complex numbers.
```julia
julia> @vars x y
(x, y)

julia> acr = @acrule((~y)^(~n) * ~y => (~y)^(~n+1))
ACRule((~y) ^ ~n * ~y => (~y) ^ (~n + 1))

julia> acr(x^2 * y * x)
((x ^ 3) * y)
```

### RuleSets

Rules are applied to an entire term, they do not see sub-terms
```julia
julia> using SymbolicUtils

julia> @vars x y
(x, y)

julia> r = @rule sin(~x) => cos(~x)
sin(~x) => cos(~x)

julia> r(sin(sin(sin(y))))
cos(sin(sin(y)))
```
however, SymbolicUtils also defines a `RuleSet` type which stores a `Vector` of rules. `RuleSets` 
when applied to terms will recursively walk through the expression and apply each of it's
consitituent rules until the term stops changing.
```julia
julia> R = RuleSet([r, @rule(~x + 1 => ~x - 1)])
RuleSet(SymbolicUtils.AbstractRule[sin(~x) => cos(~x), ~x + 1 => ~x - 1])

julia> R(sin(sin(sin(x + 1))))
cos(cos(cos((-1 + x))))
```
You can use the keyword argument `depth` to set a maximum number of recursions that a `RuleSet` is
allowed to do
```julia
julia> R(sin(sin(sin(x -1))), depth=2)
cos(cos(sin((x + -1))))
```

## Type conversion interface

This section is for Julia package developers who may want to use the `simplify` and rule rewriting system on their own expression types.

The following functions should be defined for `T` to work.

### `istree(x::T)`

Check if `x` represents an expression tree. If returns true,
it will be assumed that `operation(::T)` and `arguments(::T)`
methods are defined. Definining these three should allow use
of `simplify` on custom types. Optionally `symtype(x)` can be
defined to return the expected type of the symbolic expression.

### `operation(x::T)`

Returns the operation (a function object) performed by an expression
tree. Called only if `istree(::T)` is true. Part of the API required
for `simplify` to work. Other required methods are `arguments` and `istree`

### `arguments(x::T)`

Returns the arguments (a `Vector`) for an expression tree.
Called only if `istree(x)` is `true`. Part of the API required
for `simplify` to work. Other required methods are `operation` and `istree`


### Optional

### `symtype(x)`

The supposed type of values in the domain of x. Tracing tools can use this type to
pick the right method to run or analyse code.

This defaults to `typeof(x)` if `x` is numeric, or `Any` otherwise.
For the types defined in this package, namely `T<:Symbolic{S}` it is `S`.

Define this for your symbolic types if you want `simplify` to apply rules
specific to numbers (such as commutativity of multiplication). Or such
rules that may be implemented in the future.

### `promote_symtype(f, arg_symtypes...)`

Returns the appropriate output type of applying `f` on arguments of type `arg_symtypes`.
