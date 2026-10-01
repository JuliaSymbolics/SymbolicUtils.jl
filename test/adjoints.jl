using SymbolicUtils, SymbolicUtils.Code
using Zygote
using ChainRulesCore
using Test: @inferred

@testset "create_array adjoint" begin
  elems = (1,2,3,4,5,)

  Ts = (Float64, Float32, Float16, Int64, Int32)
  dims_candidates = ((1, (2,3)), (2, (1,3)))
  As = (Array,)

  for T in Ts,
      dims in dims_candidates,
      A in As

    u, dim = dims
    ŷ, pb = Zygote.pullback(elems) do elems
      SymbolicUtils.Code.create_array(A, T, Val(u), Val(dim), elems...)
    end
    y = SymbolicUtils.Code.create_array(A, T, Val(u), Val(dim), elems...)
    @test y == ŷ

    gs = pb(ones(T, length(elems)))
    @test length(gs[1]) == length(elems)
    for i = 1:(prod(dim)-1)
      @test gs[1][i] == one(eltype(ŷ))
    end
  end
end

@testset "create_array rrule tangent count and stability (#684)" begin
  # Vector path (Val{1}): pullback must return 5 + N tangents, type-stable.
  y, pb = ChainRulesCore.rrule(Code.create_array, Vector, nothing, Val{1}(), Val{(2,)}(), 1.0, 2.0)
  @test y == [1.0, 2.0]
  Δ = [3.0, 4.0]
  tangents = @inferred pb(Δ)
  @test length(tangents) == 5 + 2
  @test tangents[6:7] == (3.0, 4.0)
  @test all(t -> t isa ChainRulesCore.NoTangent, tangents[1:5])

  # Matrix path (Val{2}): linear indexing of the cotangent covers reshape layout.
  y2, pb2 = ChainRulesCore.rrule(Code.create_array, Array, Float64, Val{2}(), Val{(2, 2)}(),
                                 1.0, 2.0, 3.0, 4.0)
  @test y2 == Float64[1.0 3.0; 2.0 4.0]
  Δ2 = ones(2, 2)
  tangents2 = @inferred pb2(Δ2)
  @test length(tangents2) == 5 + 4
  @test tangents2[6:9] == (1.0, 1.0, 1.0, 1.0)
  @test all(t -> t isa ChainRulesCore.NoTangent, tangents2[1:5])
end

@testset "symbolic call adjoint" begin
  @syms t::Real x::Real u(::Real, ::Real)::Real
  # A term built from symbolic args carries no numeric dependency, so it can be
  # constructed inside a differentiated function and discarded (MethodOfLines#309).
  y, g = Zygote.withgradient(p -> (u(t, x); 2p), 1.0)
  @test y == 2.0
  @test g == (2.0,)
  # Numeric args are intentionally NOT marked non-differentiable: the call stores
  # them as Const (recoverable via arguments/unwrap_const, which ForwardDiff and
  # ReverseDiff differentiate through), so NoTangent would silently zero real
  # gradients. Such calls must stay outside withgradient (hoist).
end
