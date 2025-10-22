# API Reference

## Symbols and Terms

### Creating Symbols and Terms
```@docs; canonical=false
SymbolicUtils.@syms
SymbolicUtils.term
```

### Metadata
```@docs
SymbolicUtils.hasmetadata
SymbolicUtils.getmetadata
SymbolicUtils.setmetadata
```

### Type Promotion
```@docs; canonical=false
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
SymbolicUtils.simplify_fractions
SymbolicUtils.quick_cancel
SymbolicUtils.flatten_fractions
```
