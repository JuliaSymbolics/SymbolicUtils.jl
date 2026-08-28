using SciMLTesting
using SymbolicUtils

run_qa(
    SymbolicUtils;
    ei_kwargs = (;
        no_implicit_imports = (; allow_unanalyzable = (SymbolicUtils.BasicSymbolicImpl,)),
        no_stale_explicit_imports = (; ignore = (:children,), allow_unanalyzable = (SymbolicUtils.BasicSymbolicImpl,)),
        all_qualified_accesses_via_owners = (; ignore = (:copy,)),
        all_qualified_accesses_are_public = (;
            ignore = (
                Symbol("@__doc__"), Symbol("@compiler_options"), Symbol("@nany"),
                Symbol("@nexprs"), Symbol("@nospecializeinfer"), Symbol("@deprecate_binding"),
                :Commutative,
                :Compiler, :Experimental, :CreationOrder, :Monomial, :StaticArray,
                # SparseArrays dispatches `map` on these non-public types; the symbolic
                # `map` intersections have to name them to resolve.
                :AbstractCompressedVector, :AbstractSparseMatrixCSC, :FixedSparseCSC, :Slice,
                :_setindex!, :acos, :acosh, :asin, :atanh, :copy, :cos, :eval,
                :hash_abstractarray_seed, :hasha_seed, :ht_keyindex2,
                :ht_keyindex2_shorthash!, :instantiate, :kwcall, :lgamma, :literal_pow,
                :log, :log1p, :log10, :log2, :mul_prod, :pow, :postwalk,
                :promote_typejoin, :return_type, :show_unquoted, :sin, :sqrt, :tan,
                :typed_hcat, :typed_hvncat, :typed_hvcat, :typed_vcat, :RefValue, :add_sum,
                :ReinterpretArray, :ReshapedArray, :promote_eltypeof, :promote_typeof,
                # Public in Julia 1.12, but not marked public on supported Julia 1.11.
                :filter, :map, :peel, :reverse,
            ),
        ),
    ),
    # These polynomial aliases are part of the documented developer conversion
    # interface; the underlying representations are owned by DynamicPolynomials.
    reexports_allow = (
        :arguments, :iscall, :operation, :sorted_arguments,
        :ACDict, :MonomialOrder, :MonomialT, :PolyCoeffT, :PolyVarOrder,
        :PolyVarT, :PolynomialT, :ROArgsT, :TypeT,
    ),
)
