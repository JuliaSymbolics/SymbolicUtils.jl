module SymbolicUtilsLabelledArraysExt

using LabelledArrays
using LabelledArrays.StaticArrays
using SymbolicUtils

@inline function SymbolicUtils.Code.create_array(A::Type{<:SLArray}, T, nd::Val, d::Val{dims}, elems...) where {dims}
    a = SymbolicUtils.Code.create_array(SArray, T, nd, d, elems...)
    if nfields(dims) === ndims(A)
        similar_type(A, eltype(a), Size(dims))(a)
    else
        a
    end
end

@inline function SymbolicUtils.Code.create_array(A::Type{<:LArray}, T, nd::Val, d::Val{dims}, elems...) where {dims}
    data = SymbolicUtils.Code.create_array(Array, T, nd, d, elems...)
    if nfields(dims) === ndims(A)
        LArray{eltype(data),nfields(dims),typeof(data),LabelledArrays.symnames(A)}(data)
    else
        data
    end
end

end
