using SciMLTesting
using SymbolicUtils

run_qa(
    SymbolicUtils;
    # The untyped three-argument `Base.ImmutableDict` constructor is a deliberate
    # compatibility method kept for downstream packages; see `src/types.jl`.
    aqua_kwargs = (; piracies = (; treat_as_own = [Base.ImmutableDict],)),
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
                :_setindex!, :acos, :acosh, :asin, :atanh, :copy, :cos, :eval,
                :hash_abstractarray_seed, :hasha_seed, :ht_keyindex2,
                :ht_keyindex2_shorthash!, :instantiate, :kwcall, :lgamma, :literal_pow,
                :log, :log1p, :log10, :log2, :mul_prod, :pow, :postwalk,
                :promote_typejoin, :return_type, :show_unquoted, :sin, :sqrt, :tan,
                :typed_hcat, :typed_hvncat, :typed_hvcat, :typed_vcat, :RefValue, :add_sum,
                :ReinterpretArray, :ReshapedArray, :promote_eltypeof, :promote_typeof,
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
