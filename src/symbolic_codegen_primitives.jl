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
