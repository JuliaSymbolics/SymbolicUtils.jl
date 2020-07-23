@def title = "SymbolicUtils.jl — Interfacing"
@def hasmath = false
@def hascode = true
<!-- Note: by default hasmath == true and hascode == false. You can change this in
the config file by setting hasmath = false for instance and just setting it to true
where appropriate -->

# Interfacing with SymbolicUtils.jl

\tableofcontents <!-- you can use \toc as well -->

This section is for Julia package developers who may want to use the `simplify` and rule rewriting system on their own expression types.

If not directly using `@syms` and methods defined on symbols, **the easiest way to interface with SymbolicUtils  is to convert your symbolic types into SymbolicUtils' types, perform the desired rewrites, and convert back to the original types.**

This may sound like a roundabout way of doing it, but it can be really fast. In our experements with using this package to impliment simplification for [ModelingToolkit.jl](https://mtk.sciml.ai/dev/) the conversion accounted for about 3% of the total time taken for `simplify`. This approach also means that you don't ahve to take for face value the assumptions and reservations of SymbolicUtils.

## Defining the interface

SymbolicUtils matchers can match any Julia object that implements an interface to traverse it as a tree.

In particular, the following methods should be defined for an expression tree type `T` with symbol types `S` to  work
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

In addition, the methods for `Base.hash` and `Base.isequal` should also be implemented by the types for the purposes of substitution and equality matching respectively.

### Optional

#### `similarterm(t::MyType, f, args)`

Construct a new term with the operation `f` and arguments `args`, the term should be similar to `t` in type. if `t` is a `Term` object a new Term is created with the same symtype as `t`. If not, the result is computed as `f(args...)`. Defining this method for your term type will reduce any performance loss in performing `f(args...)` (esp. the splatting, and redundant type computation).

The below two functions are internal to SymbolicUtils

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

\out{piracy1}

How can we use SymbolicUtils.jl to convert `ex` to `(-)(:x, 1)`? We simply implement `istree`,
`operation`, `arguments` and `to_symbolic` and we'll be off to the races:
```julia:piracy2
using SymbolicUtils
using SymbolicUtils: istree, operation, arguments, similarterm

SymbolicUtils.istree(ex::Expr) = ex.head == :call
SymbolicUtils.operation(ex::Expr) = ex.args[1]
SymbolicUtils.arguments(ex::Expr) = ex.args[2:end]

@show simplify(ex)

dump(simplify(ex))
```

There was no simplification, because by default SymbolicUtils assumes that the expressoins are of type Any and no particular rules apply. Let's change this by saying that the symbolic type (symtype) of an Expr or Symbol object is actually Real.

```julia:piracy4
SymbolicUtils.symtype(s::Expr) = Real

dump(simplify(ex))
```
\out{piracy4}

Now SymbolicUtils is able to apply the Number simplification rule to Expr.
