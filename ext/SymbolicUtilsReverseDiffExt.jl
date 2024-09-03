module SymbolicUtilsReverseDiffExt

using ReverseDiff
using SymbolicUtils

@inline function SymbolicUtils.Code.create_array(::Type{<:ReverseDiff.TrackedArray}, T, v1::Val, v2::Val{dims}, elems...) where dims
    SymbolicUtils.ArrayInterface.aos_to_soa(SymbolicUtils.Code.create_array(Array, T, v1, v2, elems...))
end

end
