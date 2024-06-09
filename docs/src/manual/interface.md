# Interfacing with SymbolicUtils.jl

This section is for Julia package developers who may want to use the `simplify` and rule rewriting system on their own expression types.

## Defining the interface

SymbolicUtils matchers can match any Julia object that implements an interface to traverse it as a tree. The interface in question, is defined in the [TermInterface.jl](https://github.com/JuliaSymbolics/TermInterface.jl) package. Its purpose is to provide a shared interface between various symbolic programming Julia packages. 

In particular, you should define methods from TermInterface.jl for an expression tree type `T` with symbol types `S` to  work
with SymbolicUtils.jl

You can read the documentation of [TermInterface.jl](https://github.com/JuliaSymbolics/TermInterface.jl) on the [Github repository](https://github.com/JuliaSymbolics/TermInterface.jl).

## SymbolicUtils.jl only methods

### `symtype(x)`

Returns the symbolic type of `x`. By default this is just `typeof(x)`.
Define this for your symbolic types if you want `SymbolicUtils.simplify` to apply rules
specific to numbers (such as commutativity of multiplication). Or such
rules that may be implemented in the future.

### `issym(x)`

Returns `true` if `x` is a symbol. If true, `nameof` must be defined
on `x` and must return a Symbol.

### `promote_symtype(f, arg_symtypes...)`

Returns the appropriate output type of applying `f` on arguments of type `arg_symtypes`.
