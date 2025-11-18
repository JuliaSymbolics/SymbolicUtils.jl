const NonTreeSym = Union{BasicSymbolic{SymReal}, BasicSymbolic{SafeReal}}

import Base: (+), (-), (*), (//), (/), (\), (^)

@generated function _numeric_or_arrnumeric_type(S::TypeT)
    @nospecialize S
    
    expr = Expr(:if)
    cur_expr = expr
    push!(cur_expr.args, :(S === Number))
    push!(cur_expr.args, true)
    new_expr = Expr(:elseif)
    push!(cur_expr.args, new_expr)
    cur_expr = new_expr

    push!(cur_expr.args, :(S === Real))
    push!(cur_expr.args, true)
    new_expr = Expr(:elseif)
    push!(cur_expr.args, new_expr)
    cur_expr = new_expr

    push!(cur_expr.args, :(S === Vector{Number}))
    push!(cur_expr.args, true)
    new_expr = Expr(:elseif)
    push!(cur_expr.args, new_expr)
    cur_expr = new_expr

    push!(cur_expr.args, :(S === Vector{Real}))
    push!(cur_expr.args, true)
    new_expr = Expr(:elseif)
    push!(cur_expr.args, new_expr)
    cur_expr = new_expr

    push!(cur_expr.args, :(S === Matrix{Number}))
    push!(cur_expr.args, true)
    new_expr = Expr(:elseif)
    push!(cur_expr.args, new_expr)
    cur_expr = new_expr

    push!(cur_expr.args, :(S === Matrix{Real}))
    push!(cur_expr.args, true)
    new_expr = Expr(:elseif)
    push!(cur_expr.args, new_expr)
    cur_expr = new_expr

    i = 0
    
    N = length(SCALARS)
    for t1 in SCALARS
        for T in [t1, Vector{t1}, Matrix{t1}, LinearAlgebra.UniformScaling{t1}]
            i += 1
            push!(cur_expr.args, :(S === $T))
            push!(cur_expr.args, true)
            i == 4N && continue
            new_expr = Expr(:elseif)
            push!(cur_expr.args, new_expr)
            cur_expr = new_expr
        end
    end
    push!(cur_expr.args, :(S <: Union{Number, AbstractArray{<:Number}}))
    quote
        @nospecialize S
        $expr
    end
end

function _numeric_or_arrnumeric_symtype(x)
    if x isa Array{<:BasicSymbolic}
        all(_numeric_or_arrnumeric_symtype, x)
    else
        _numeric_or_arrnumeric_type(symtype(x))
    end
end

@generated function _rational_or_arrrational_type(S::TypeT)
    @nospecialize S
    
    expr = Expr(:if)
    cur_expr = expr
    i = 0
    N = length(SCALARS)
    for t1 in SCALARS
        for T in [t1, Vector{t1}, Matrix{t1}, LinearAlgebra.UniformScaling{t1}]
            i += 1
            push!(cur_expr.args, :(S === $T))
            push!(cur_expr.args, t1 <: Rat)
            i == 4N && continue
            new_expr = Expr(:elseif)
            push!(cur_expr.args, new_expr)
            cur_expr = new_expr
        end
    end
    push!(cur_expr.args, :(S <: Union{Rat, AbstractArray{<:Rat}}))
    quote
        @nospecialize S
        $expr
    end
end

function _rational_or_arrrational_symtype(x)
    if x isa Array{<:BasicSymbolic}
        all(_rational_or_arrrational_symtype, x)
    else
        _rational_or_arrrational_type(symtype(x))
    end
end

abstract type Operator end
promote_shape(::Operator, @nospecialize(shx::ShapeT)) = shx
promote_symtype(::Operator, ::Type{T}) where {T} = T
