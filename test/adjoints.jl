using SymbolicUtils, SymbolicUtils.Code
using Zygote

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

@testset "symbolic call adjoint" begin
  @syms t::Real x::Real u(::Real, ::Real)::Real
  # a term built inside a differentiated function carries no derivative, whether its
  # arguments are symbolic or numbers stored in the term
  for f in (p -> (u(t, x); 2p), p -> (u(p, x); 2p))
    y, g = Zygote.withgradient(f, 1.0)
    @test y == 2.0
    @test g == (2.0,)
  end
end
