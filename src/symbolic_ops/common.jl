const NonTreeSym = Union{BasicSymbolic{SymReal}, BasicSymbolic{SafeReal}}

import Base: (+), (-), (*), (//), (/), (\), (^)

macro __generate_numeric_or_arrrnumeric_type()
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

    return esc(expr)
end

function _numeric_or_arrnumeric_type(@nospecialize(S::TypeT))
    @__generate_numeric_or_arrrnumeric_type
end

function _numeric_or_arrnumeric_symtype(x)
    if x isa Array{<:BasicSymbolic}
        all(_numeric_or_arrnumeric_symtype, x)
    else
        _numeric_or_arrnumeric_type(symtype(x))
    end
end

macro __generate_rational_or_arrrational_type()
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
    return esc(expr)
end

function _rational_or_arrrational_type(@nospecialize(S::TypeT))
    @__generate_rational_or_arrrational_type
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
