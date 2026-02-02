@noinline function throw_unequal_shape_error(x, y)
    throw(ArgumentError("Cannot add arguments of different sizes - encountered shapes $x and $y."))
end

promote_shape(::typeof(+), shape::ShapeT) = shape
function promote_shape(::typeof(+), sh1::ShapeT, sh2::ShapeT, shs::ShapeT...)
    @nospecialize sh1 sh2 shs
    nd1 = _ndims_from_shape(sh1)
    nd2 = _ndims_from_shape(sh2)
    nd1 == -1 || nd2 == -1 || nd1 == nd2 || throw_unequal_shape_error(sh1, sh2)
    if sh1 isa Unknown && sh2 isa Unknown
        promote_shape(+, Unknown(max(nd1, nd2)), shs...)
    elseif sh1 isa Unknown
        promote_shape(+, sh2, shs...)
    elseif sh2 isa Unknown
        promote_shape(+, sh1, shs...)
    else
        new_shape = ShapeVecT()
        sizehint!(new_shape, length(sh1))
        for (shi, shj) in zip(sh1, sh2)
            length(shi) == length(shj) || throw_unequal_shape_error(sh1, sh2)
            # resultant shape is always 1-indexed for consistency
            push!(new_shape, 1:length(shi))
        end
        promote_shape(+, new_shape, shs...)
    end
end
promote_shape(::typeof(-), args::ShapeT...) = promote_shape(+, args...)

function +(x::T, args::Union{Number, T, AbstractArray{<:Number}, AbstractArray{T}}...) where {T <: NonTreeSym}
    add_worker(vartype(T), (x, args...))
end

@noinline Base.@nospecializeinfer function promoted_symtype(op, terms)
    a, bs = Iterators.peel(terms)
    type::TypeT = symtype(a)
    for b in bs
        type = promote_symtype(op, type, symtype(b))
    end
    return type
end

mutable struct AddWorkerBuffer{T}
    dict::ACDict{T}
end

AddWorkerBuffer{T}() where {T} = AddWorkerBuffer{T}(ACDict{T}())

Base.empty!(awb::AddWorkerBuffer) = empty!(awb.dict)

const SYMREAL_ADDBUFFER = TaskLocalValue{AddWorkerBuffer{SymReal}}(AddWorkerBuffer{SymReal})
const SAFEREAL_ADDBUFFER = TaskLocalValue{AddWorkerBuffer{SafeReal}}(AddWorkerBuffer{SafeReal})

"""
    $METHODLIST

Add an indexable list or tuple of terms `terms` with the given vartype. Applicable only for
symbolic expressions with numeric or array of numeric symtype.
"""
add_worker(::Type{SymReal}, terms) = SYMREAL_ADDBUFFER[](terms)
add_worker(::Type{SafeReal}, terms) = SAFEREAL_ADDBUFFER[](terms)

function _added_shape(terms::Tuple)
    promote_shape(+, ntuple(shape ∘ Base.Fix1(getindex, terms), Val(length(terms)))...)
end

function _added_shape(terms)
    isempty(terms) && return Unknown(-1)
    length(terms) == 1 && return shape(first(terms))
    a, bs = Iterators.peel(terms)
    sh::ShapeT = shape(a)
    for t in bs
        sh = promote_shape(+, sh, shape(t))
    end
    return sh
end

function (awb::AddWorkerBuffer{T})(terms) where {T}
    if !all(_numeric_or_arrnumeric_symtype, terms)
        throw(MethodError(+, Tuple(terms)))
    end
    isempty(terms) && return zero_of_vartype(T)
    if isone(length(terms))
        return Const{T}(only(terms))
    end
    empty!(awb)
    shape = _added_shape(terms)
    type::TypeT = symtype(Const{T}(first(terms)))
    # type = promoted_symtype(+, terms)
    newcoeff = 0
    result = awb.dict
    for term in terms
        term = unwrap(term)
        if _is_array_of_symbolics(term)
            term = Const{T}(term)
        end
        type = promote_symtype(+, type, symtype(term))
        if term isa BasicSymbolic{T}
            @match term begin
                BSImpl.Const(; val) => (newcoeff = newcoeff .+ val)
                BSImpl.AddMul(; coeff, dict, variant, shape, type, metadata) => begin
                    @match variant begin
                        AddMulVariant.ADD => begin
                            newcoeff += coeff
                            for (k, v) in dict
                                result[k] = get(result, k, 0) + v
                            end
                        end
                        AddMulVariant.MUL => begin
                            newterm = Mul{T}(1, dict; shape, type, metadata)
                            result[newterm] = get(result, newterm, 0) + coeff
                        end
                    end
                end
                _ => begin
                    result[term] = get(result, term, 0) + 1
                end
            end
        elseif term isa BasicSymbolic{SymReal} || term isa BasicSymbolic{SafeReal} || term isa BasicSymbolic{TreeReal}
            error("Cannot operate on symbolics with different vartypes. Found `$T` and `$(vartype(term))`.")
        elseif term isa AbstractIrrational
            term = BSImpl.Term{T}(identity, ArgsT{T}((Const{T}(term),)); type = Real, shape = ShapeVecT())
            result[term] = get(result, term, 0) + 1
        else
            newcoeff += term
        end
    end
    filter!(!(iszero ∘ last), result)
    isempty(result) && return Const{T}(newcoeff)
    var = Add{T}(newcoeff, result; type, shape)::BasicSymbolic{T}
    @match var begin
        BSImpl.AddMul(; dict) && if dict === result end => (awb.dict = ACDict{T}())
        _ => nothing
    end
    return var
end

const PolyadicNumericOpFirstArgT{T} = Union{Number, AbstractArray{<:Number}, AbstractArray{T}}

for T in [:(PolyadicNumericOpFirstArgT{T}), Int, Float64, Bool]
    @eval function +(a::$T, b::T, bs...) where {T <: NonTreeSym}
        return add_worker(vartype(T), (a, b, bs...))
    end
end

function -(a::BasicSymbolic{T}) where {T}
    if !_numeric_or_arrnumeric_symtype(a)
        throw(MethodError(-, (symtype(a),)))
    end
    @match a begin
        BSImpl.Const(; val) => Const{T}(-val)
        _ => nothing
    end
    @match a begin
        BSImpl.AddMul(; coeff, dict, variant, shape, type) => begin
            @match variant begin
                AddMulVariant.ADD => begin
                    coeff = -coeff
                    dict = copy(dict)
                    map!(-, values(dict))
                    return BSImpl.AddMul{T}(coeff, dict, variant; shape, type)
                end
                AddMulVariant.MUL => begin
                    return Mul{T}(-coeff, dict; shape, type)::BasicSymbolic{T}
                end
            end
        end
        _ => (-1 * a)::BasicSymbolic{T}
    end
end

function -(a::S, b::S) where {S <: NonTreeSym}
    if !_numeric_or_arrnumeric_symtype(a) || !_numeric_or_arrnumeric_symtype(b)
        throw(MethodError(-, (a, b)))
    end
    T = vartype(S)
    @match (a, b) begin
        (BSImpl.Const(; val = val1), BSImpl.Const(; val = val2)) => begin
            return Const{T}(val1 - val2)
        end
        _ => return add_worker(T, (a, -b))::BasicSymbolic{T}
    end
end

-(a::Union{Number, AbstractArray{<:Number}}, b::BasicSymbolic) = a + (-b)
-(a::BasicSymbolic, b::Union{Number, AbstractArray{<:Number}}) = a + (-b)
function -(a::AbstractArray{<:BasicSymbolic}, b::BasicSymbolic)
    Const{vartype(b)}(a) + (-b)
end
function -(a::BasicSymbolic, b::AbstractArray{<:BasicSymbolic})
    a - Const{vartype(a)}(b)
end
