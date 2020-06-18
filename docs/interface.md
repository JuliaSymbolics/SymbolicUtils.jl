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

SymbolicUtils uses a function `to_symbolic` to convert aribtrarty types to it's own internal types. Our intention is for SymbolicUtils to be useful even for packages with their own custom symbolic types which
differ from those offered by SymbolicUtils. To this end, SymbolicUtils provides an interface which if implemented, will enable automatic conversion of types to SymbolicUtils types.

*  an `operation`, (i.e. function to apply)
* `arguments` which the `operation` is applied to
* `variable` types which are the atoms from which the expression tree is built 
* optionally, a type which should `typeof(operation(arguments...))` should return if it were to be run.

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
using SymbolicUtils: Sym, Term, istree, operation, arguments, to_symbolic

SymbolicUtils.istree(ex::Expr) = ex.head == :call
SymbolicUtils.operation(ex::Expr) = ex.args[1]
SymbolicUtils.arguments(ex::Expr) = ex.args[2:end]
SymbolicUtils.to_symbolic(s::Symbol) = Sym(s)

@show simplify(ex)

dump(simplify(ex))
```
\out{piracy2}

this thing returns a `Term{Any}`, but it's not hard to convert back to `Expr`:

```julia:piracy3
to_expr(t::Term) = Expr(:call, operation(t), to_expr.(arguments(t))...) 
to_expr(x) = x

@show expr = to_expr(simplify(ex))

dump(expr)
```
\out{piracy3}


Now suppose we actaully wanted all `Symbol`s to be treated as `Real` numbers. We can simply define
```julia:piracy4
SymbolicUtils.symtype(s::Symbol) = Real

dump(simplify(ex))
```
\out{piracy4}

and now all our analysis is able to figure out that the `Term`s are `Number`s.
