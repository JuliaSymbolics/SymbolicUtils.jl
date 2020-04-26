# SymbolicUtils.jl

SymbolicUtils.jl provides various utilities for symbolic computing.

[![Build Status](https://travis-ci.org/JuliaSymbolics/SymbolicUtils.jl.svg?branch=master)](https://travis-ci.com/github/JuliaSymbolics/SymbolicUtils.jl)  [![Coverage Status](https://coveralls.io/repos/github/JuliaSymbolics/SymbolicUtils.jl/badge.svg?branch=master)](https://coveralls.io/github/JuliaSymbolics/SymbolicUtils.jl?branch=master)

## Symbols and expressions

Symbols can be created using the `@syms` macro:

```julia
julia> using SymbolicUtils

julia> @syms a::Integer b c d x::Real y::Number
(a, b, c, d, x, y)
```

This macro also defines the Julia variables of the same name and each is set to the its respective symbolic object.

The associated type `T` in the `@syms a::T` syntax, called `symtype` of the symbol, is the type the value of the symbol is supposed to be of. These types may determine the rules of symbolic simplification.

Arithmetic and math functions are defined on symbols and return `Term` objects which represent function call expressions.

Symbols can be defined to behave like functions. Both the input and output types for the function can be specified. Any application to that function will only admit either values of those types or symbols of the same `symtype`.

```julia
julia> @syms f(x) g(x::Real, y::Real)::Real
(f(::Number)::Number, g(::Real, ::Real)::Real)

julia> f(c)
f(c)

julia> g(1, x)
g(1, x)
```

## Symbolic simplification

Use the `simplify` function to apply a built in list of rules to simplify an expression:
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
julia> @syms a b c
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
julia> @syms x y
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

julia> @syms x y
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

## Interfacing with SymbolicUtils.jl

This section is for Julia package developers who may want to use the `simplify` and rule rewriting system on their own expression types.

Our intention is for SymbolicUtils to be useful even for packages with their own custom symbolic types which
differ from those offered by SymbolicUtils. To this end, SymbolicUtils provides an interface to convert expression
tree types which have 
*  an `operation`, (i.e. function to apply)
* `arguments` which the `operation` is applied to
* `variable` types which are the atoms from which the expression tree is built 
* optionally, a type which should `typeof(operation(arguments...))` should return if it were to be run.

SymbolicUtils uses a function `to_symbolic` to convert aribtrarty types to it's own internal types. 

The following methods should be defined for an expression tree type `T` with symbol types `S` to  work
with SymbolicUtils.jl

#### `istree(x::T)`

Check if `x` represents an expression tree. If returns true,
it will be assumed that `operation(::T)` and `arguments(::T)`
methods are defined. Definining these three should allow use
of `simplify` on custom types. Optionally `symtype(x)` can be
defined to return the expected type of the symbolic expression.

#### `operation(x::T)`

Returns the operation (a function object) performed by an expression
tree. Called only if `istree(::T)` is true. Part of the API required
for `simplify` to work. Other required methods are `arguments` and `istree`

#### `arguments(x::T)`

Returns the arguments (a `Vector`) for an expression tree.
Called only if `istree(x)` is `true`. Part of the API required
for `simplify` to work. Other required methods are `operation` and `istree`

#### `to_symbolic(x::S)`
Convert your variable type to a `SymbolicUtils.Sym`. Suppose you have
```julia
struct MySymbol
   s::Symbol
end
```
which could represent any type symbolically, then you would define 
```julia
SymbolicUtils.to_symbolic(s::MySymbol) = SymbolicUtils.Sym(s.s)
```

### Optional

#### `symtype(x)`

The supposed type of values in the domain of x. Tracing tools can use this type to
pick the right method to run or analyse code.

This defaults to `typeof(x)` if `x` is numeric, or `Any` otherwise.
For the types defined in this package, namely `T<:Symbolic{S}` it is `S`.

Define this for your symbolic types if you want `simplify` to apply rules
specific to numbers (such as commutativity of multiplication). Or such
rules that may be implemented in the future.

#### `promote_symtype(f, arg_symtypes...)`

Returns the appropriate output type of applying `f` on arguments of type `arg_symtypes`.

### Example

Suppose you were feeling the temptations of type piracy and wanted to make a quick and dirty
symbolic library built on top of Julia's `Expr` type, e.g.

```julia
for f ∈ [:+, :-, :*, :/, :^] #Note, this is type piracy!
    @eval begin
        Base.$f(x::Union{Expr, Symbol}, y::Number) = Expr(:call, $f, x, y)
        Base.$f(x::Number, y::Union{Expr, Symbol}) = Expr(:call, $f, x, y)
        Base.$f(x::Union{Expr, Symbol}, y::Union{Expr, Symbol}) = (Expr(:call, $f, x, y))
    end
end


julia> ex = 1 + (:x - 2)
:((+)(1, (-)(x, 2)))
```
How can we use SymbolicUtils.jl to convert `ex` to `(-)(:x, 1)`? We simply implement `istree`,
`operation`, `arguments` and `to_symbolic` and we'll be off to the races:
```julia
using SymbolicUtils: Sym, istree, operation, arguments, to_symbolic

SymbolicUtils.istree(ex::Expr) = ex.head == :call
SymbolicUtils.operation(ex::Expr) = ex.args[1]
SymbolicUtils.arguments(ex::Expr) = ex.args[2:end]
SymbolicUtils.to_symbolic(s::Symbol) = Sym(s)

julia> simplify(ex)
(-1 + x)

julia> dump(simplify(ex))
Term{Any}
  f: + (function of type typeof(+))
  arguments: Array{Any}((2,))
    1: Int64 -1
    2: Sym{Any}
      name: Symbol x
```
this thing returns a `Term{Any}`, but it's not hard to convert back to `Expr`:
```julia
to_expr(t::Term) = Expr(:call, operation(t), to_expr.(arguments(t))...) 
to_expr(x) = x

julia> to_expr(simplify(ex))
:((+)(-1, x))

julia> dump(ans)
Expr
  head: Symbol call
  args: Array{Any}((3,))
    1: + (function of type typeof(+))
    2: Int64 -1
    3: Symbol x
```

Now suppose we actaully wanted all `Symbol`s to be treated as `Real` numbers. We can simply define
```julia
SymbolicUtils.symtype(s::Symbol) = Real

julia> dump(simplify(ex))
Term{Real}
  f: + (function of type typeof(+))
  arguments: Array{Any}((2,))
    1: Int64 -1
    2: Sym{Real}
      name: Symbol x
```
and now all our analysis is able to figure out that the `Term`s are `Number`s.

# Citations

- The pattern matcher is an adaption of the one by Gerald Jay Sussman (as seen in [6.945](https://groups.csail.mit.edu/mac/users/gjs/6.945/) at MIT), his use of symbolic programming in the book [SICM](https://groups.csail.mit.edu/mac/users/gjs/6946/sicm-html/book.html) inspired this package.
- [Rewrite.jl](https://github.com/HarrisonGrodin/Rewrite.jl) and [Simplify.jl](https://github.com/HarrisonGrodin/Simplify.jl) by [Harrison Grodin](https://github.com/HarrisonGrodin) also inspired this package.
