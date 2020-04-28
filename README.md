<h1 align="center"><a href="https://juliasymbolics.github.io/SymbolicUtils.jl/">SymbolicUtils.jl</a></h1>

[![Build Status](https://travis-ci.org/JuliaSymbolics/SymbolicUtils.jl.svg?branch=master)](https://travis-ci.com/github/JuliaSymbolics/SymbolicUtils.jl)  [![Coverage Status](https://coveralls.io/repos/github/JuliaSymbolics/SymbolicUtils.jl/badge.svg?branch=master)](https://coveralls.io/github/JuliaSymbolics/SymbolicUtils.jl?branch=master)
<p align="center">
  <a href="https://travis-ci.com/github/JuliaSymbolics/SymbolicUtils.jl">
    <img src="https://travis-ci.org/JuliaSymbolics/SymbolicUtils.jl.svg?branch=master"
         alt="Build Status (Linux)">
  </a>
  <a href="https://ci.appveyor.com/project/tlienart/Franklin-jl">
    <img src="https://ci.appveyor.com/api/projects/status/github/tlienart/Franklin.jl?branch=master&svg=true"
         alt="Build Status (Windows)">
  </a>
  <a href="https://coveralls.io/github/JuliaSymbolics/SymbolicUtils.jl?branch=master">
    <img src="https://coveralls.io/repos/github/JuliaSymbolics/SymbolicUtils.jl/badge.svg?branch=master"
         alt="Coverage">
  </a>
</p>

SymbolicUtils.jl provides various utilities for symbolic computing.

[![Build Status](https://travis-ci.org/JuliaSymbolics/SymbolicUtils.jl.svg?branch=master)](https://travis-ci.com/github/JuliaSymbolics/SymbolicUtils.jl)  [![Coverage Status](https://coveralls.io/repos/github/JuliaSymbolics/SymbolicUtils.jl/badge.svg?branch=master)](https://coveralls.io/github/JuliaSymbolics/SymbolicUtils.jl?branch=master)

[Symbols in SymbolicUtils](https://juliasymbolics.github.io/SymbolicUtils.jl/#creating_symbolic_expressions) carry type information. Operations on them propagate this information. [A rule-based rewriting language](https://juliasymbolics.github.io/SymbolicUtils.jl/#rule-based_rewriting) can be used to find subexpressions that satisfy arbitrary conditions and apply arbitrary transformations on the matches. The library also contains a set of useful [simplification](https://juliasymbolics.github.io/SymbolicUtils.jl/#simplification) rules for expressions of numeric symbols and numbers. These can be remixed and extended for special purposes.

If you are a Julia package develper in need of a rule rewriting system for your own types, have a look at the [interfacing guide](https://juliasymbolics.github.io/SymbolicUtils.jl/interface/).

[**Go to the manual**](https://juliasymbolics.github.io/SymbolicUtils.jl/)

# Citations

- The pattern matcher is an adaption of the one by Gerald Jay Sussman (as seen in [6.945](https://groups.csail.mit.edu/mac/users/gjs/6.945/) at MIT), his use of symbolic programming in the book [SICM](https://groups.csail.mit.edu/mac/users/gjs/6946/sicm-html/book.html) inspired this package.
- [Rewrite.jl](https://github.com/HarrisonGrodin/Rewrite.jl) and [Simplify.jl](https://github.com/HarrisonGrodin/Simplify.jl) by [Harrison Grodin](https://github.com/HarrisonGrodin) also inspired this package.
