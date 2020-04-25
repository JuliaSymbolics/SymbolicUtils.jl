# SymbolicUtils.jl

SymbolicUtils.jl provides various utilities for symbolic computing.

## Symbolic simplification

```julia
julia> using SymbolicUtils

julia> @vars a::Integer b c d x::Real y::Number
(a, b, c, d, x, y)

julia> simplify(a + b + (x * y) + c + 2 * (x * y) + d + sin(x)^2 + cos(x)^2 - y^0)
((3 * x * y) + a + b + c + d)
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

## `operation(x::T)`

Returns the operation (a function object) performed by an expression
tree. Called only if `istree(::T)` is true. Part of the API required
for `simplify` to work. Other required methods are `arguments` and `istree`

## `arguments(x::T)`

Returns the arguments (a `Vector`) for an expression tree.
Called only if `istree(x)` is `true`. Part of the API required
for `simplify` to work. Other required methods are `operation` and `istree`


### Optional

## `symtype(x)`

The supposed type of values in the domain of x. Tracing tools can use this type to
pick the right method to run or analyse code.

This defaults to `typeof(x)` if `x` is numeric, or `Any` otherwise.
For the types defined in this package, namely `T<:Symbolic{S}` it is `S`.

Define this for your symbolic types if you want `simplify` to apply rules
specific to numbers (such as commutativity of multiplication). Or such
rules that may be implemented in the future.

## `promote_symtype(f, arg_symtypes...)`

Returns the appropriate output type of applying `f` on arguments of type `arg_symtypes`.
