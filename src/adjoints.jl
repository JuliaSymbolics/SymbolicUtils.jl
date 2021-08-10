using ChainRulesCore
import ChainRulesCore: rrule
import .Code

function rrule(::typeof(Code.create_array), A::Type{<:AbstractArray}, T, u::Val{j}, d::Val{dims}, elems...) where {dims, j}
  y = Code.create_array(A, T, u, d, elems...)
  function create_array_pullback(Δ)
    dx = Δ
    (ZeroTangent(), NoTangent(), NoTangent(), NoTangent(), NoTangent(), dx..., ntuple(_ -> NoTangent(), length(elems) - prod(dims) + j)...)
  end
  y, create_array_pullback
end
