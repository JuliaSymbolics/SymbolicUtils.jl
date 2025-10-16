struct __InternalInvalidator1 <: Real end
struct __InternalInvalidator2 <: AbstractArray{Real, 1} end
struct __InternalInvalidator3 <: AbstractArray{Number, 2} end
struct __InternalInvalidator4 <: Operator end
struct __InternalInvalidator5 <: Operator end
struct __InternalInvalidator6 <: Operator end
symtype(::__InternalInvalidator1) = _unreachable()
symtype(::__InternalInvalidator2) = _unreachable()
symtype(::__InternalInvalidator3) = _unreachable()
symtype(::Vector{Int}) = Vector{Int}
symtype(::Matrix{Float64}) = Matrix{Float64}
symtype(::Array{UInt, 3}) = Array{UInt, 3}
symtype(::Int) = Int
symtype(::Float64) = Float64
symtype(::UInt) = UInt
unwrap(::__InternalInvalidator1) = _unreachable()
unwrap(::__InternalInvalidator2) = _unreachable()
unwrap(::__InternalInvalidator3) = _unreachable()
unwrap(x::AbstractArray{Int}) = x
unwrap(x::AbstractArray{Float64}) = x
unwrap(x::AbstractArray{UInt}) = x
unwrap(x::Int) = x
unwrap(x::Float64) = x
unwrap(x::UInt) = x
(::Rule)(::__InternalInvalidator1) = _unreachable()
(::Rule)(::__InternalInvalidator2) = _unreachable()
(::Rule)(::__InternalInvalidator3) = _unreachable()
(::ACRule)(::__InternalInvalidator1) = _unreachable()
(::ACRule)(::__InternalInvalidator2) = _unreachable()
(::ACRule)(::__InternalInvalidator3) = _unreachable()
promote_symtype(::__InternalInvalidator1, args...) = _unreachable()
promote_symtype(::__InternalInvalidator2, args...) = _unreachable()
promote_symtype(::__InternalInvalidator3, args...) = _unreachable()
Base.convert(::Type{__InternalInvalidator1}, ::BasicSymbolic) = _unreachable()
Base.convert(::Type{Int}, ::BasicSymbolic) = _unreachable()
Base.convert(::Type{Float64}, ::BasicSymbolic) = _unreachable()
Base.convert(::Type{UInt}, ::BasicSymbolic) = _unreachable()
expand(x::Int, _...) = x
expand(x::Complex{Int}, _...) = x
expand(x::Complex{Float64}, _...) = x
simplify(x::Int; _...) = x
simplify(x::Complex{Int}; _...) = x
simplify(x::Complex{Float64}; _...) = x
isbinop(::Int) = false
isbinop(::String) = false
isbinop(::__InternalInvalidator1) = false
operator_to_term(::__InternalInvalidator4, ::BasicSymbolic) = _unreachable()
operator_to_term(::__InternalInvalidator5, ::BasicSymbolic) = _unreachable()
operator_to_term(::__InternalInvalidator6, ::BasicSymbolic) = _unreachable()
