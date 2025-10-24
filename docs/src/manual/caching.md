# Caching recursive functions

Many functions benefit greatly from caching their results such that repeated calls with the same arguments
can return cached values. As an example, `getindex` on symbolic arrays is a cached function since the operation can
be expensive. SymbolicUtils.jl provides the `@cache` macro to allow easily caching such functions, with special
benefits when the arguments are symbolic.

```@docs
SymbolicUtils.@cache
SymbolicUtils.associated_cache
SymbolicUtils.get_limit
SymbolicUtils.set_limit
SymbolicUtils.get_retain_fractions
SymbolicUtils.set_retain_fractions
SymbolicUtils.toggle_caching
SymbolicUtils.is_caching_enabled
SymbolicUtils.clear_cache
```
