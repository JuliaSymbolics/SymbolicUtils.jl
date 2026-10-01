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

# Pullback must return exactly 1 + 4 + N tangents with N known at compile time.
# Splatting a runtime-length cotangent Vector (and padding with `+ j` NoTangents)
# made the return type a Vararg union and returned one-too-many tangents, which
# Zygote silently tolerated at a large allocation cost (JuliaSymbolics/SymbolicUtils.jl#684).
function rrule(::typeof(Code.create_array), A::Type{<:AbstractArray}, T, u::Val{j}, d::Val{dims},
               elems::Vararg{Any,N}) where {dims, j, N}
  y = Code.create_array(A, T, u, d, elems...)
  function create_array_pullback(Δ)
    dx = unthunk(Δ)
    (NoTangent(), NoTangent(), NoTangent(), NoTangent(), NoTangent(), ntuple(i -> dx[i], Val(N))...)
  end
  y, create_array_pullback
end

end
