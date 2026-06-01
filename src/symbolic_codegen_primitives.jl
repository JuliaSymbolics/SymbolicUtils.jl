function SymbolicUtils.promote_symtype(::Type{Assignment}, lhs_type::TypeT, rhs_type::TypeT)
    return rhs_type
end

function SymbolicUtils.promote_shape(::Type{Assignment}, @nospecialize(_lhs_shape::ShapeT), rhs_shape::ShapeT)
    @nospecialize rhs_shape
    return rhs_shape
end

"""
    symAssignment(lhs, rhs)

Construct a symbolic expression representing `lhs = rhs`. Returns a
`Term{T}(Code.Assignment, [lhs, rhs])` with `symtype` and `shape` equal to those of `rhs`.
"""
function symAssignment(lhs::BasicSymbolic{T}, rhs::BasicSymbolic{T}) where {T}
    return BSImpl.Term{T}(
        Assignment, ArgsT{T}((lhs, rhs));
        type = symtype(rhs),
        shape = shape(rhs)
    )
end
function symAssignment(lhs::BasicSymbolic{T}, rhs) where {T}
    return symAssignment(lhs, BSImpl.Const{T}(rhs))
end
function symAssignment(lhs, rhs::BasicSymbolic{T}) where {T}
    return symAssignment(BSImpl.Const{T}(lhs), rhs)
end

function SymbolicUtils.promote_symtype(::Type{Func}, args_type::TypeT, body_type::TypeT)
    @assert args_type <: Tuple
    return FnType{args_type, body_type, Nothing}::TypeT
end

function SymbolicUtils.promote_shape(::Type{Func}, @nospecialize(_args_shape::ShapeT), body_shape::ShapeT)
    @nospecialize body_shape
    return body_shape
end

"""
    symFunc(args, body)

Construct a symbolic expression representing an anonymous function with argument list `args`
and body `body`. `args` must be an iterable of symbolic variables. Returns a
`Term{T}(Code.Func, [args_term, body])` where `args_term = term(tuple, args...)`, with
`symtype` `FnType{symtype(args_term), symtype(body), Nothing}` and `shape` equal to
`shape(body)`.
"""
function symFunc(args::BasicSymbolic{T}, body::BasicSymbolic{T}) where {T}
    return BSImpl.Term{T}(
        Func, ArgsT{T}((args, body));
        type = SymbolicUtils.promote_symtype(Func, symtype(args), symtype(body)),
        shape = SymbolicUtils.promote_shape(Func, shape(args), shape(body))
    )
end
function symFunc(args::Union{AbstractArray, Tuple}, body::BasicSymbolic{T}) where {T}
    return symFunc(
        BSImpl.Term{T}(
            tuple, args;
            type = SymbolicUtils.promote_symtype(tuple, symtype.(args)...),
            shape = ShapeVecT((1:length(args),))
        ), body
    )
end
function symFunc(args::BasicSymbolic{T}, body) where {T}
    return symFunc(args, BSImpl.Const{T}(body))
end
