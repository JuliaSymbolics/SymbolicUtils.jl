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

```@docs
SymbolicUtils.Code.toexpr
```

## Code Combinators

These are all exported when you do `using SymbolicUtils.Code`

```@docs
SymbolicUtils.Code.Assignment
SymbolicUtils.Code.Let
SymbolicUtils.Code.Func
SymbolicUtils.Code.SpawnFetch
SymbolicUtils.Code.SetArray
SymbolicUtils.Code.MakeArray
SymbolicUtils.Code.MakeSparseArray
SymbolicUtils.Code.MakeTuple
SymbolicUtils.Code.LiteralExpr
```