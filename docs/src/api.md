# API Reference

## Symbols and Terms

### Creating Symbols and Terms
```@docs
SymbolicUtils.@syms
SymbolicUtils.term
SymbolicUtils.Sym
```

### Inspecting Terms
```@docs
SymbolicUtils.issym
SymbolicUtils.symtype
SymbolicUtils.iscall
SymbolicUtils.operation
SymbolicUtils.arguments
SymbolicUtils.sorted_arguments
SymbolicUtils.showraw
```

### Term Types
```@docs
SymbolicUtils.Term
SymbolicUtils.Add
SymbolicUtils.Mul
SymbolicUtils.Pow
```

### Metadata
```@docs
SymbolicUtils.hasmetadata
SymbolicUtils.getmetadata
SymbolicUtils.setmetadata
```

### Type Promotion
```@docs
SymbolicUtils.promote_symtype
```

## Rewriting System

### Rule Creation
```@docs
@rule
@acrule
```

### Rewriters
```@docs
SymbolicUtils.Rewriters
SymbolicUtils.Rewriters.Empty
SymbolicUtils.Rewriters.IfElse
SymbolicUtils.Rewriters.If
SymbolicUtils.Rewriters.Chain
SymbolicUtils.Rewriters.RestartedChain
SymbolicUtils.Rewriters.Fixpoint
SymbolicUtils.Rewriters.FixpointNoCycle
SymbolicUtils.Rewriters.Postwalk
SymbolicUtils.Rewriters.Prewalk
SymbolicUtils.Rewriters.PassThrough
```

## Simplification and Transformation

```@docs
SymbolicUtils.simplify
SymbolicUtils.expand
SymbolicUtils.substitute
```

## Polynomial Forms

```@docs
SymbolicUtils.PolyForm
SymbolicUtils.simplify_fractions
SymbolicUtils.quick_cancel
SymbolicUtils.flatten_fractions
```

## Code Generation

### Core Functions
```@docs
SymbolicUtils.toexpr
SymbolicUtils.cse
```

### Code Generation Types
```@docs
SymbolicUtils.Assignment
SymbolicUtils.Let
SymbolicUtils.Func
SymbolicUtils.DestructuredArgs
SymbolicUtils.LiteralExpr
SymbolicUtils.ForLoop
```

### Array Operations
```@docs
SymbolicUtils.SetArray
SymbolicUtils.MakeArray
SymbolicUtils.MakeSparseArray
SymbolicUtils.MakeTuple
```

### Parallelism
```@docs
SymbolicUtils.SpawnFetch
SymbolicUtils.Multithreaded
```

## Utilities

```@docs
SymbolicUtils.@timerewrite
```