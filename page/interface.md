@def title = "SymbolicUtils.jl — Interfacing"
@def hasmath = false
@def hascode = true
<!-- Note: by default hasmath == true and hascode == false. You can change this in
the config file by setting hasmath = false for instance and just setting it to true
where appropriate -->

# Interfacing with SymbolicUtils.jl

\tableofcontents <!-- you can use \toc as well -->

This section is for Julia package developers who may want to use the `simplify` and rule rewriting system on their own expression types.

## Defining the interface

SymbolicUtils matchers can match any Julia object that implements an interface to traverse it as a tree.

In particular, the following methods should be defined for an expression tree type `T` with symbol types `S` to  work
with SymbolicUtils.jl

#### `isterm(x::T)`

Check if `x` represents an expression tree. If returns true,
it will be assumed that `head(::T)` and `arguments(::T)`
methods are defined. Definining these three should allow use
of `simplify` on custom types. Optionally `symtype(x)` can be
defined to return the expected type of the symbolic expression.

#### `head(x::T)`

Returns the head (a function object) performed by an expression
tree. Called only if `isterm(::T)` is true. Part of the API required
for `simplify` to work. Other required methods are `arguments` and `isterm`

#### `arguments(x::T)`

Returns the arguments (a `Vector`) for an expression tree.
Called only if `isterm(x)` is `true`. Part of the API required
for `simplify` to work. Other required methods are `gethead` and `isterm`

In addition, the methods for `Base.hash` and `Base.isequal` should also be implemented by the types for the purposes of substitution and equality matching respectively.

#### `similarterm(t::MyType, f, args[, T])`

Construct a new term with the operation `f` and arguments `args`, the term should be similar to `t` in type. if `t` is a `Term` object a new Term is created with the same symtype as `t`. If not, the result is computed as `f(args...)`. Defining this method for your term type will reduce any performance loss in performing `f(args...)` (esp. the splatting, and redundant type computation). T is the symtype of the output term. You can use `promote_symtype` to infer this type.

The below two functions are internal to SymbolicUtils

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

## Example

Suppose you were feeling the temptations of type piracy and wanted to make a quick and dirty
symbolic library built on top of Julia's `Expr` type, e.g.

```julia:piracy1
for f ∈ [:+, :-, :*, :/, :^] #Note, this is type piracy!
    @eval begin
        Base.$f(x::Union{Expr, Symbol}, y::Number) = Expr(:call, $f, x, y)
        Base.$f(x::Number, y::Union{Expr, Symbol}) = Expr(:call, $f, x, y)
        Base.$f(x::Union{Expr, Symbol}, y::Union{Expr, Symbol}) = (Expr(:call, $f, x, y))
    end
end


ex = 1 + (:x - 2)
```


How can we use SymbolicUtils.jl to convert `ex` to `(-)(:x, 1)`? We simply implement `isterm`,
`head`, `arguments` and we'll be able to do rule-based rewriting on `Expr`s:
```julia:piracy2
using SymbolicUtils

SymbolicUtils.isterm(ex::Expr) = ex.head == :call
SymbolicUtils.head(ex::Expr) = ex.args[1]
SymbolicUtils.arguments(ex::Expr) = ex.args[2:end]

@rule(~x => ~x - 1)(ex)
```

However, this is not enough to get SymbolicUtils to use its own algebraic simplification system on `Expr`s:
```julia:piracy3
simplify(ex)
```

The reason that the expression was not simplified is that the expression tree is untyped, so SymbolicUtils 
doesn't know what rules to apply to the expression. To mimic the behaviour of most computer algebra 
systems, the simplest thing to do would be to assume that all `Expr`s are of type `Number`:

```julia:piracy4
SymbolicUtils.symtype(s::Expr) = Number

simplify(ex)
```

Now SymbolicUtils is able to apply the `Number` simplification rule to `Expr`.
