# Developer API

The names on this page are public extension points for packages that build on
SymbolicUtils, including Symbolics.jl. They are intentionally not generally
exported. User code should prefer the higher-level symbolic constructors,
rewriters, and substitution APIs documented on the main [API page](@ref "API Reference").

## Expression and cache interfaces

```@docs; canonical=false
SymbolicUtils.:<ₑ
SymbolicUtils.@cache
SymbolicUtils.ACDict
SymbolicUtils.AddMulVariant
SymbolicUtils.ArgsT
SymbolicUtils.BSImpl
SymbolicUtils.BasicSymbolicImpl
SymbolicUtils.Const
SymbolicUtils.Div
SymbolicUtils.MetadataT
SymbolicUtils.Operator
SymbolicUtils.ROArgsT
SymbolicUtils.Substituter
SymbolicUtils.Term
SymbolicUtils.TypeT
SymbolicUtils._isone
SymbolicUtils._iszero
SymbolicUtils.clear_cache!
SymbolicUtils.default_is_atomic
SymbolicUtils.default_substitute_filter
SymbolicUtils.evaluate
SymbolicUtils.get_substitution_dict
SymbolicUtils.hashcons
SymbolicUtils.is_array_shape
SymbolicUtils.is_function_symbolic
SymbolicUtils.is_called_function_symbolic
SymbolicUtils.isarrayop
SymbolicUtils.isbinop
SymbolicUtils.numerators
SymbolicUtils.denominators
SymbolicUtils.one_of_vartype
SymbolicUtils.operation_getname
SymbolicUtils.operation_hasname
SymbolicUtils.operator_to_term
SymbolicUtils.promote_symtype
SymbolicUtils.query
SymbolicUtils.scalarize
SymbolicUtils.search_variables
SymbolicUtils.search_variables!
SymbolicUtils.show_call
SymbolicUtils.stable_eachindex
SymbolicUtils.toggle_caching!
SymbolicUtils.zero_of_vartype
SymbolicUtils.zeropoly
```

## Parsing and polynomial conversion

```@docs; canonical=false
SymbolicUtils.MonomialOrder
SymbolicUtils.MonomialT
SymbolicUtils.PolyCoeffT
SymbolicUtils.PolyVarOrder
SymbolicUtils.PolyVarT
SymbolicUtils.PolynomialT
SymbolicUtils._indexed_ndims
SymbolicUtils.basicsymbolic_to_polyvar
SymbolicUtils.from_poly
SymbolicUtils.parse_variable
SymbolicUtils.sym_from_parse_result
SymbolicUtils.to_poly!
```

## Rewriting and broadcasting helpers

```@docs; canonical=false
SymbolicUtils.@map_methods
SymbolicUtils.@mapreduce_methods
SymbolicUtils.@number_methods
SymbolicUtils.number_methods
SymbolicUtils.Rule
SymbolicUtils.SymBroadcast
```

## Code generation

```@docs; canonical=false
SymbolicUtils.Code
SymbolicUtils.Code.LazyState
SymbolicUtils.Code.cse_inside_expr
SymbolicUtils.Code.fast_toexpr
SymbolicUtils.Code.function_to_expr
SymbolicUtils.Code.get_rewrites
SymbolicUtils.Code.supports_with_allocator
SymbolicUtils.Code.with_allocator
```
