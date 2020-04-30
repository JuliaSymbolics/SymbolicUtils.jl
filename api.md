@def title = "SymbolicUtils.jl — API"
@def hasmath = false
@def hascode = true

# API Reference

## Symbolic types and expressions

```julia:load_symutils
using SymbolicUtils # hide
```

{{doc @syms @syms macro}}

{{doc Sym Sym type}}

{{doc symtype symtype fn}}

{{doc Term Term type}}

{{doc promote_symtype promote_symtype fn}}

# Interfacing

{{doc to_symbolic to_symbolic fn}}

{{doc istree istree fn}}

{{doc operation operation fn}}

{{doc arguments arguments fn}}

## Rules

{{doc @rule @rule macro}}

{{doc RuleSet RuleSet type}}

{{doc simplify simplify fn}}

## Utilities

{{doc @timerewrite @timerewrite macro}}
