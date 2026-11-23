using SymbolicUtils
using SymbolicUtils: SymBroadcast, SymReal
using Test
using JET

@syms w::Real

# Concrete array + Ref rule: the typed materialize / Tuple path used by `substitute.(X, rule)`.
const _sub_Xv = [SymbolicUtils.Sym{SymReal}(Symbol(:x, i); type = Real) for i in 1:4]
const _sub_rule = Ref(w => -w)
const _sub_args = (_sub_Xv, _sub_rule)
const _sub_bc = Broadcast.Broadcasted{SymBroadcast{SymReal}}(substitute, _sub_args)

@testset "JET: substitute broadcast materialize args" begin
    # Specialized `_materialize_substitute_broadcast_arg` methods (replaces `@nospecialize`).
    @test_opt SymbolicUtils._materialize_substitute_broadcast_arg(SymReal, _sub_Xv)
    @test_opt SymbolicUtils._materialize_substitute_broadcast_arg(SymReal, _sub_rule)
end

@testset "JET: eager substitute.(arr, rule) materialization" begin
    # Tuple-specialized eager entry used by `_copy_broadcast!` for `typeof(substitute)`.
    # Full `@test_opt` on this call is dominated by known `substitute`/`hashconsing`
    # runtime dispatches; JET also does not flag `Core._apply_iterate` splats of
    # `Vector{Any}` (the old `@nospecialize` path). Guard that regression via inference:
    # the typed path returns a concrete array, the old splat infers `Any`.
    @test Core.Compiler.return_type(
        SymbolicUtils._eager_substitute_broadcast_args,
        Tuple{Type{SymReal}, typeof(_sub_args)},
    ) <: AbstractArray
    @test (@inferred Broadcast.copy(_sub_bc)) isa Vector
end
