module SymbolicUtilsChainRulesCoreExt

using ChainRulesCore
import ChainRulesCore: rrule
import SymbolicUtils.Code
using SymbolicUtils: BasicSymbolic

# Calling a symbolic function with only symbolic arguments builds a term with no
# numeric dependency, so it is safe to treat as opaque to reverse-mode AD.
# This lets `sol[u(t, x)]`-style terms be built inside a differentiated function
# without hoisting (SciML/MethodOfLines.jl#309).
# Do NOT extend to numeric args: the call stores them as `Const` (recoverable via
# `arguments`/`unwrap_const`, which ForwardDiff/ReverseDiff differentiate through),
# so `NoTangent` would silently zero real gradients. Numeric-arg calls stay outside
# `withgradient` and error if traced, rather than returning wrong gradients.
ChainRulesCore.@non_differentiable (f::BasicSymbolic)(args::BasicSymbolic...)

function rrule(::typeof(Code.create_array), A::Type{<:AbstractArray}, T, u::Val{j}, d::Val{dims}, elems...) where {dims, j}
  y = Code.create_array(A, T, u, d, elems...)
  function create_array_pullback(Δ)
    dx = Δ
    (ZeroTangent(), NoTangent(), NoTangent(), NoTangent(), NoTangent(), dx..., ntuple(_ -> NoTangent(), length(elems) - prod(dims) + j)...)
  end
  y, create_array_pullback
end

end
