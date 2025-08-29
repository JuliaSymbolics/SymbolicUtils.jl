 # SymbolicUtils.jl 

[![Join the chat at https://julialang.zulipchat.com #sciml-bridged](https://img.shields.io/static/v1?label=Zulip&message=chat&color=9558b2&labelColor=389826)](https://julialang.zulipchat.com/#narrow/stream/279055-sciml-bridged)
[![Global Docs](https://img.shields.io/badge/docs-SciML-blue.svg)](https://docs.sciml.ai/SymbolicUtils/stable/)

[![codecov](https://codecov.io/gh/JuliaSymbolics/SymbolicUtils.jl/branch/master/graph/badge.svg)](https://app.codecov.io/gh/JuliaSymbolics/SymbolicUtils.jl)
[![Build Status](https://github.com/JuliaSymbolics/SymbolicUtils.jl/workflows/CI/badge.svg)](https://github.com/JuliaSymbolics/SymbolicUtils.jl/actions?query=workflow%3ACI)
[![Build status](https://badge.buildkite.com/3db222e469784b365e4b45f2b0155d252cf0ae70fef708bfa1.svg?branch=master)](https://buildkite.com/julialang/symbolicutils-dot-jl)

[![ColPrac: Contributor's Guide on Collaborative Practices for Community Packages](https://img.shields.io/badge/ColPrac-Contributor%27s%20Guide-blueviolet)](https://github.com/SciML/ColPrac)
[![SciML Code Style](https://img.shields.io/static/v1?label=code%20style&message=SciML&color=9558b2&labelColor=389826)](https://github.com/SciML/SciMLStyle)


## Tutorials and Documentation

For information on using the package,
[see the stable documentation](https://docs.sciml.ai/SymbolicUtils/stable/). Use the
[in-development documentation](https://docs.sciml.ai/SymbolicUtils/dev/) for the version of
the documentation, which contains the unreleased features.

SymbolicUtils.jl provides various utilities for symbolic computing. SymbolicUtils.jl is what one would use to build
a Computer Algebra System (CAS). If you're looking for a complete CAS, similar to SymPy or Mathematica, see
[Symbolics.jl](https://github.com/JuliaSymbolics/Symbolics.jl). If you want to build a crazy CAS for your weird
Octonian algebras, you've come to the right place.

[Symbols in SymbolicUtils](https://docs.sciml.ai/SymbolicUtils/stable/#Creating-symbolic-expressions) carry type information. Operations on them propagate this information. [A rule-based rewriting language](https://docs.sciml.ai/SymbolicUtils/stable/manual/rewrite/) can be used to find subexpressions that satisfy arbitrary conditions and apply arbitrary transformations on the matches. The library also contains a set of useful [simplification](https://docs.sciml.ai/SymbolicUtils/stable/#Simplification) rules for expressions of numeric symbols and numbers. These can be remixed and extended for special purposes.

If you are a Julia package developer in need of a rule rewriting system for your own types, have a look at the [interfacing guide](https://docs.sciml.ai/SymbolicUtils/stable/manual/interface/#Interfacing-with-SymbolicUtils.jl).


### "I don't want to read your manual, just show me some cool code"
```julia
julia> using SymbolicUtils

julia> SymbolicUtils.show_simplified[] = true

julia> @syms x::Real y::Real z::Complex f(::Number)::Real
(x, y, z, f(::Number)::Real)

julia> 2x^2 - y + x^2
(3 * (x ^ 2)) + (-1 * y)

julia> f(sin(x)^2 + cos(x)^2) + z
f(1) + z

julia> r = @rule sinh(im * ~x) => sin(~x)
sinh(im * ~x) => sin(~x)

julia> r(sinh(im * y))
sin(y)

julia> simplify(cos(y)^2 + sinh(im*y)^2, RuleSet([r]))
1
```

# Citations

- The pattern matcher is an adaption of the one by Gerald Jay Sussman (as seen in [6.945](https://groups.csail.mit.edu/mac/users/gjs/6.945/) at MIT), his use of symbolic programming in the book [SICM](https://groups.csail.mit.edu/mac/users/gjs/6946/sicm-html/book.html) inspired this package.
- [Rewrite.jl](https://github.com/HarrisonGrodin/Rewrite.jl) and [Simplify.jl](https://github.com/HarrisonGrodin/Simplify.jl) by [Harrison Grodin](https://github.com/HarrisonGrodin) also inspired this package.
