@def title = "SymbolicUtils.jl — API"
@def hasmath = false
@def hascode = true

# API Reference

\tableofcontents

## Symbols and Terms

```julia:load_symutils
using SymbolicUtils # hide
```

{{doc @syms @syms macro}}

{{doc Sym Sym type}}

{{doc symtype symtype fn}}

{{doc Term Term type}}

{{doc promote_symtype promote_symtype fn}}

## Interfacing

{{doc to_symbolic to_symbolic fn}}

{{doc istree istree fn}}

{{doc operation operation fn}}

{{doc arguments arguments fn}}

## Rewriters

{{doc @rule @rule macro}}

{{doc Rewriters module}}

## Simplify

{{doc simplify simplify fn}}

{{doc substitute substitute fn}}

## Utilities

{{doc @timerewrite @timerewrite macro}}
