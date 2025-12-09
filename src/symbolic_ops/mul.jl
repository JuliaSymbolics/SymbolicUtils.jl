*(a::BasicSymbolic) = a

@noinline function throw_expected_matrix(x)
    throw(ArgumentError("Expected matrix in multiplication, got argument of shape $x."))
end
@noinline function throw_expected_matvec(x)
    throw(ArgumentError("""
    Expected matrix or vector in multiplication, got argument of shape $x.
    """))
end
@noinline function throw_incompatible_shapes(x, y)
    throw(ArgumentError("""
    Encountered incompatible shapes $x and $y when multiplying.
    """))
end

is_array_shape(sh::ShapeT) = sh isa Unknown || _ndims_from_shape(sh) > 0
function _multiplied_shape(shapes)
    first_arr = findfirst(is_array_shape, shapes)
    first_arr === nothing && return ShapeVecT(), first_arr, nothing
    last_arr::Int = findlast(is_array_shape, shapes)
    first_arr == last_arr && return shapes[first_arr], first_arr, last_arr

    sh1::ShapeT = shapes[first_arr]
    shend::ShapeT = shapes[last_arr]
    ndims_1 = _ndims_from_shape(sh1)
    ndims_end = _ndims_from_shape(shend)
    # Vector * transpose(Vector) works
    ndims_1 == -1 || ndims_1 == 2 || ndims_1 == 1 || throw_expected_matrix(sh1)
    ndims_end <= 2 || throw_expected_matvec(shend)
    if ndims_end == 1
        # NOTE: This lies because the shape of a matvec mul isn't solely determined by the
        # shapes of inputs. If the first array is an adjoint or transpose, the result
        # is a scalar.
        result = sh1 isa Unknown ? Unknown(1) : ShapeVecT((sh1[1],))
    elseif sh1 isa Unknown || shend isa Unknown
        result = Unknown(ndims_end)
    else
        result = ShapeVecT((first(sh1), last(shend)))
    end
    cur_shape = sh1
    is_matmatmul = ndims_1 != 1
    for i in (first_arr + 1):last_arr
        sh = shapes[i]
        ndims_sh = _ndims_from_shape(sh)
        is_array_shape(sh) || continue
        ndims_sh <= 2 || throw_expected_matvec(shend)
        if is_matmatmul
            if cur_shape isa ShapeVecT && sh isa ShapeVecT
                if length(last(cur_shape)) != length(first(sh))
                    throw_incompatible_shapes(cur_shape, sh)
                end
            end
        else
            ndims_sh == 2 || throw_incompatible_shapes(cur_shape, sh)
            if cur_shape isa ShapeVecT && sh isa ShapeVecT
                length(first(sh)) == 1 || throw_incompatible_shapes(cur_shape, sh)
            end
        end
        is_matmatmul = ndims_sh != 1
        cur_shape = sh
    end

    return result, first_arr, last_arr
end

function promote_shape(::typeof(*), shs::ShapeT...)
    _multiplied_shape(shs)[1]
end

const AdjointOrTranspose = Union{LinearAlgebra.Adjoint, LinearAlgebra.Transpose}

function _check_adjoint_or_transpose(terms, result::ShapeT, first_arr::Union{Int, Nothing}, last_arr::Union{Int, Nothing})
    @nospecialize first_arr result last_arr
    first_arr === nothing && return result
    last_arr = last_arr::Int
    first_arr == last_arr && return result
    farr = terms[first_arr]
    ndlarr = ndims(terms[last_arr])
    if result isa ShapeVecT && length(result) <= 2 && all(isone ∘ length, result) && (farr isa AdjointOrTranspose || iscall(farr) && (operation(farr) === adjoint || operation(farr) === transpose)) && ndlarr < 2
        return ShapeVecT()
    end
    return result
end

function _multiplied_terms_shape(terms::Tuple)
    result, first_arr, last_arr = _multiplied_shape(ntuple(shape ∘ Base.Fix1(getindex, terms), Val(length(terms))))
    return _check_adjoint_or_transpose(terms, result, first_arr, last_arr)
end

function _multiplied_terms_shape(terms)
    shapes = SmallV{ShapeT}()
    sizehint!(shapes, length(terms))
    for t in terms
        push!(shapes, shape(t))
    end
    result, first_arr, last_arr = _multiplied_shape(shapes)
    return _check_adjoint_or_transpose(terms, result, first_arr, last_arr)
end

function _split_arrterm_scalar_coeff(::Type{T}, ex::BasicSymbolic{T}) where {T}
    sh = shape(ex)
    is_array_shape(sh) || return ex, one_of_vartype(T)
    @match ex begin
        BSImpl.Term(; f, args, type) && if f === (*) && !is_array_shape(shape(first(args))) end => begin
            if length(args) == 2
                return args[1], args[2]
            end
            rest = ArgsT{T}()
            sizehint!(rest, length(args) - 1)
            coeff, restargs = Iterators.peel(args)
            for arg in restargs
                push!(rest, arg)
            end
            return coeff, Term{T}(f, rest; type, shape = sh)
        end
        BSImpl.ArrayOp(; output_idx, expr, reduce, term, ranges, shape, type) => begin
            coeff, rest = @match expr begin
                BSImpl.Term(; f, args, type, shape) && if f === (*) end => begin
                    if query(isequal(idxs_for_arrayop(T)), args[1])
                        one_of_vartype(T), expr
                    elseif length(args) == 2
                        args[1], args[2]
                    else
                        newargs = ArgsT{T}()
                        _coeff, rest = Iterators.peel(args)
                        append!(newargs, rest)
                        _coeff, BSImpl.Term{T}(*, newargs; type, shape)
                    end
                end
                _ => (one_of_vartype(T), expr)
            end
            if term === nothing
                termrest = nothing
            else
                termcoeff, termrest = _split_arrterm_scalar_coeff(T ,term)
                @assert isequal(termcoeff, coeff)
            end
            return coeff, BSImpl.ArrayOp{T}(output_idx, rest, reduce, termrest, ranges; shape, type)
        end
        _ => (one_of_vartype(T), ex)
    end
end
_split_arrterm_scalar_coeff(::Type{T}, ex) where {T} = one_of_vartype(T), Const{T}(ex)

function _mul_worker!(::Type{T}, num_coeff, den_coeff, num_dict, den_dict, term) where {T}
    @nospecialize term
    if term isa BasicSymbolic{T}
        @match term begin
            BSImpl.Const(; val) => (num_coeff[] *= val)
            BSImpl.AddMul(; coeff, dict, variant) && if variant == AddMulVariant.MUL end => begin
                num_coeff[] *= coeff
                for (k, v) in dict
                    num_dict[k] = get(num_dict, k, 0) + v
                end
            end
            BSImpl.Term(; f, args) && if f === (^) && !isconst(args[1]) && isconst(args[2]) end => begin
                base, exp = args
                num_dict[base] = get(num_dict, base, 0) + unwrap_const(exp)
            end
            BSImpl.Div(; num, den) => begin
                _mul_worker!(T, num_coeff, den_coeff, num_dict, den_dict, num)
                _mul_worker!(T, den_coeff, num_coeff, den_dict, num_dict, den)
            end
            x => begin
                num_dict[x] = get(num_dict, x, 0) + 1
            end
        end
    elseif term isa BasicSymbolic{SymReal} || term isa BasicSymbolic{SafeReal}
        error("Cannot operate on symbolics with different vartypes. Found `$T` and `$(vartype(term))`.")
    elseif term isa AbstractIrrational
        base = BSImpl.Term{T}(identity, ArgsT{T}((Const{T}(term),)); type = Real, shape = ShapeVecT())
        num_dict[base] = get(num_dict, base, 0) + 1
    else
        num_coeff[] *= term
    end
    return nothing
end

mutable struct MulWorkerBuffer{T}
    num_dict::ACDict{T}
    den_dict::ACDict{T}
    const arrterms::Vector{BasicSymbolic{T}}
    const num_coeff::RefValue{PolyCoeffT}
    const den_coeff::RefValue{PolyCoeffT}
end

function MulWorkerBuffer{T}() where {T}
    MulWorkerBuffer{T}(Dict{BasicSymbolic{T}, Any}(), Dict{BasicSymbolic{T}, Any}(), BasicSymbolic{T}[], Ref{PolyCoeffT}(1), Ref{PolyCoeffT}(1))
end

function Base.empty!(mwb::MulWorkerBuffer)
    empty!(mwb.num_dict)
    empty!(mwb.den_dict)
    empty!(mwb.arrterms)
    mwb.num_coeff[] = 1
    mwb.den_coeff[] = 1
    return mwb
end

const SYMREAL_MULBUFFER = TaskLocalValue{MulWorkerBuffer{SymReal}}(MulWorkerBuffer{SymReal})
const SAFEREAL_MULBUFFER = TaskLocalValue{MulWorkerBuffer{SafeReal}}(MulWorkerBuffer{SafeReal})

function (mwb::MulWorkerBuffer{T})(terms) where {T}
    if terms isa ArgsT{T}
        @union_split_smallvec terms begin
            for x in terms
                _is_array_of_symbolics(x) && continue
                _numeric_or_arrnumeric_symtype(x) && continue
                throw(MethodError(*, Tuple(symtype.(terms))))
            end
        end
    else
        for x in terms
            _is_array_of_symbolics(x) && continue
            _numeric_or_arrnumeric_symtype(x) && continue
            throw(MethodError(*, Tuple(symtype.(terms))))
        end
    end
    isempty(terms) && return one_of_vartype(T)
    length(terms) == 1 && return Const{T}(terms[1])
    empty!(mwb)
    newshape = _multiplied_terms_shape(terms)
    num_dict = mwb.num_dict
    num_coeff = mwb.num_coeff
    den_dict = mwb.den_dict
    den_coeff = mwb.den_coeff
    arrterms = mwb.arrterms

    # We're multiplying numbers here. If we don't take the `eltype`
    # and the first element is an array, `promote_symtype` may fail
    # so we take the eltype, since `scalar * scalar` and `scalar * array`
    # both give the correct result regardless of whether the first element
    # is a scalar or array.
    type::TypeT = safe_eltype(symtype(Const{T}(first(terms))))

    for term in terms
        term = unwrap(term)
        if _is_array_of_symbolics(term)
            term = Const{T}(term)
        end
        sh = shape(term)
        type = promote_symtype(*, type, symtype(term))
        if is_array_shape(sh)
            coeff, arrterm = _split_arrterm_scalar_coeff(T, term)
            _mul_worker!(T, num_coeff, den_coeff, num_dict, den_dict, coeff)
            if iscall(arrterm) && operation(arrterm) === (*)
                append!(arrterms, arguments(arrterm))
            else
                push!(arrterms, arrterm)
            end
            continue
        end
        _mul_worker!(T, num_coeff, den_coeff, num_dict, den_dict, term)
    end
    for k in keys(num_dict)
        haskey(den_dict, k) || continue
        numexp = num_dict[k]
        denexp = den_dict[k]
        if (numexp >= denexp)::Bool
            num_dict[k] = numexp - denexp
            den_dict[k] = 0
        else
            num_dict[k] = 0
            den_dict[k] = denexp - numexp
        end
    end
    filter!(kvp -> !iszero(kvp[2]), num_dict)
    filter!(kvp -> !iszero(kvp[2]), den_dict)

    ntrivialcoeff = _isone(num_coeff[])::Bool
    dtrivialcoeff = _isone(den_coeff[])::Bool
    ntrivialdict = isempty(num_dict)
    dtrivialdict = isempty(den_dict)
    ntrivial = ntrivialcoeff && ntrivialdict
    dtrivial = dtrivialcoeff && dtrivialdict

    if ntrivialcoeff && ntrivialdict
        num = one_of_vartype(T)
    elseif ntrivialdict
        num = Const{T}(num_coeff[])
    else
        num = Mul{T}(num_coeff[], num_dict; type = safe_eltype(type)::TypeT)::BasicSymbolic{T}
        @match num begin
            BSImpl.AddMul(; dict) && if dict === num_dict end => begin
                mwb.num_dict = ACDict{T}()
            end
            _ => nothing
        end
    end
    if dtrivialcoeff && dtrivialdict
        den = one_of_vartype(T)
    elseif dtrivialdict
        den = Const{T}(den_coeff[])
    else
        den = Mul{T}(den_coeff[], den_dict; type = safe_eltype(type)::TypeT)::BasicSymbolic{T}
        @match den begin
            BSImpl.AddMul(; dict) && if dict === den_dict end => begin
                mwb.den_dict = ACDict{T}()
            end
            _ => nothing
        end
    end

    if ntrivial && dtrivial
        result = one_of_vartype(T)
    elseif dtrivial
        result = num
    else
        result = Div{T}(num, den, false; type = safe_eltype(type)::TypeT)::BasicSymbolic{T}
    end

    isempty(arrterms) && return result

    scalartrivial = ntrivial && dtrivial
    new_arrterms = ArgsT{T}()
    _nontrivial_coeff = !scalartrivial
    if _nontrivial_coeff
        push!(new_arrterms, result)
    end
    cur = 2
    acc_arrterm = arrterms[1]
    acc_pow = 1
    @match acc_arrterm begin
        BSImpl.Term(; f, args) && if f === (^) && isconst(args[2]) end => begin
            acc_arrterm = args[1]
            acc_pow = unwrap_const(args[2])::Number
        end
        _ => nothing
    end
    n_arrterms = length(arrterms)
    while cur <= n_arrterms
        cur_arrterm = arrterms[cur]
        cur += 1
        @match cur_arrterm begin
            BSImpl.Term(; f, args) && if f === (^) && isequal(args[1], acc_arrterm) && isconst(args[2]) end => begin
                acc_pow += unwrap_const(args[2])
            end
            _ => begin
                if isequal(acc_arrterm, cur_arrterm)
                    acc_pow += 1
                    continue
                end
                push!(new_arrterms, _isone(acc_pow) ? acc_arrterm : (acc_arrterm ^ acc_pow))
                acc_arrterm = cur_arrterm
                acc_pow = 1
            end
        end
    end
    push!(new_arrterms, _isone(acc_pow) ? acc_arrterm : (acc_arrterm ^ acc_pow))
    if length(new_arrterms) == 1
        return new_arrterms[1]
    end
    return Term{T}(*, new_arrterms; type, shape = newshape)
end

"""
    $METHODLIST

Multiply an indexable list or tuple of terms `terms` with the given vartype. Applicable
only for symbolic expressions with numeric or array of numeric symtype.
"""
mul_worker(::Type{SymReal}, terms) = SYMREAL_MULBUFFER[](terms)
mul_worker(::Type{SafeReal}, terms) = SAFEREAL_MULBUFFER[](terms)

function *(x::T, args::Union{Number, T, AbstractArray{<:Number}, AbstractArray{T}}...) where {T <: NonTreeSym}
    mul_worker(vartype(T), (x, args...))
end

for T in [:(PolyadicNumericOpFirstArgT{T}), Int, Float64, Bool]
    @eval function *(a::$T, b::T, bs::Union{Number, T, AbstractArray{<:Number}, AbstractArray{T}}...) where {T <: NonTreeSym}
        return mul_worker(vartype(T), (a, b, bs...))
    end
end
