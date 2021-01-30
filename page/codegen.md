@def title = "SymbolicUtils.jl — Code generation"
@def hasmath = false
@def hascode = true

# Code generation

**Note: this feature is experimental and the API might change frequently**

`toexpr(ex)` turns any expression (`ex`) into the equivalent `Expr` which is suitable for `eval`. The `SymbolicUtils.Code` module provides some combinators which provides the ability to construct more complex expressions than just function calls. These include:



- Let blocks
- Functions with arguments and keyword arguments
  - Functions with arguments which are to be de-structured
- Expressions that set array elements in-place
- Expressions that create an array similar in type to a reference array (currently supports `Array`, `StaticArrays.SArray`, and `LabelledArrays.SLArray`)
- Expressions that create sparse arrays

**Do `using SymbolicUtils.Code` to get the following bindings**

## `toexpr`

{{doc toexpr toexpr fn Code}}

## Code Combinators

These are all exported when you do `using SymbolicUtils.Code`

{{doc Assignment Assignment type Code}}

{{doc Let Let type Code}}

{{doc Func Func type Code}}

{{doc SetArray SetArray type Code}}

{{doc MakeArray MakeArray type Code}}

{{doc MakeSparseArray MakeSparseArray type Code}}

{{doc MakeTuple MakeTuple type Code}}

{{doc LiteralExpr LiteralExpr type Code}}
