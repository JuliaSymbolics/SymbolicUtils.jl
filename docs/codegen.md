@def title = "SymbolicUtils.jl — Code generation"
@def hasmath = false
@def hascode = true

# Generating executable code from Symbolics

**Note: this feature is experimental and the API might change frequently**

`toexpr(ex)` turns any expression (`ex`) into the equivalent `Expr` which is suitable for `eval`. The `SymbolicUtils.Code` module provides some combinators which provides the ability to construct more complex expressions than just function calls. These include:

- Let blocks
- Functions with arguments and keyword arguments
  - Functions with arguments which are to be de-structured
- Expressions that set array elements in-place
- Expressions that create an array similar in type to a reference array (currently supports `Array`, `StaticArrays.SArray`, and `LabelledArrays.SLArray`)
- Expressions that create sparse arrays

## `toexpr(ex, [st,])`

{{doc toexpr toexpr fn}}

## Code Combinators

These are all exported when you do `using SymbolicUtils.Code`

{{doc Assignment Assignment type}}

{{doc Let Let type}}

{{doc Func Func type}}

{{doc SetArray SetArray type}}

{{doc MakeArray MakeArray type}}

{{doc MakeSparseArray MakeSparseArray type}}

{{doc MakeTuple MakeTuple type}}

{{doc LiteralExpr LiteralExpr type}}
