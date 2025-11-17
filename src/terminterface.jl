"""
    $TYPEDSIGNATURES

Extract the operation (function) from a symbolic function call expression.
Only valid for expressions where `iscall(expr)` returns `true`.

Returns the function/operator that is being applied in the expression. For basic
arithmetic, this returns the operator function (+, -, *, /, ^). For function calls
like `sin(x)`, this returns the function `sin`.

# Examples
```julia
using SymbolicUtils
@variables x y

# Arithmetic operations
expr1 = x + y
operation(expr1)    # returns +

expr2 = x * y  
operation(expr2)    # returns *

# Function calls
expr3 = sin(x)
operation(expr3)    # returns sin

# Nested expressions
expr4 = sin(x + y)
operation(expr4)    # returns sin
operation(arguments(expr4)[1])  # returns +
```

See also: [`TermInterface.iscall`](@ref), [`arguments`](@ref)
"""
@inline function TermInterface.operation(x::BSImpl.Type{T}) where {T}
    @nospecialize x
    @match x begin
        BSImpl.Const(_) => throw(ArgumentError("`Const` does not have an operation."))
        BSImpl.Sym(_) => throw(ArgumentError("`Sym` does not have an operation."))
        BSImpl.Term(; f) => f
        BSImpl.AddMul(; variant) => @match variant begin
            AddMulVariant.ADD => (+)
            AddMulVariant.MUL => (*)
        end
        BSImpl.Div(_) => (/)
        BSImpl.ArrayOp(; term) => begin
            if term === nothing
                ArrayOp{T}
            elseif term isa BasicSymbolic{T}
                operation(term)
            end
        end
    end
end

"""
    sorted_arguments(x::BasicSymbolic)

Get the arguments of a symbolic expression in canonical sorted order.

For commutative operations like addition and multiplication, the arguments
are sorted according to a canonical ordering. This ensures that equivalent
expressions have the same representation.

# Arguments
- `x::BasicSymbolic`: The symbolic expression

# Returns
A vector of the arguments in sorted order. For non-commutative operations,
returns the arguments in their original order.

# Examples
```julia
julia> @syms x y z
(x, y, z)

julia> expr = x + z + y
x + y + z

julia> sorted_arguments(expr)
3-element Vector{Any}:
 x
 y
 z
```
"""
@cache function TermInterface.sorted_arguments(x::BSImpl.Type)::ROArgsT
    T = vartype(x)
    @match x begin
        BSImpl.AddMul(; variant) => begin
            args = copy(parent(arguments(x)))
            @match variant begin
                AddMulVariant.ADD => sort!(args; by = get_degrees, lt = monomial_lt)
                AddMulVariant.MUL => sort!(args; by = get_degrees)
            end
            return ROArgsT{T}(ArgsT{T}(args))
        end
        _ => return arguments(x)
    end
end

"""
    arguments(expr)

Extract the arguments from a symbolic function call expression.
Only valid for expressions where `iscall(expr)` returns `true`.

Returns a collection (typically a vector) containing the arguments passed to the operation.
For binary operations like `+` or `*`, this returns a collection of all operands.
For function calls, this returns the function arguments.

# Examples
```julia
using SymbolicUtils
@variables x y z

# Binary arithmetic operations
expr1 = x + y
arguments(expr1)    # returns collection containing x and y

expr2 = x * y * z  
arguments(expr2)    # returns collection containing x, y, and z

# Function calls
expr3 = sin(x)
arguments(expr3)    # returns collection containing x

# Nested expressions
expr4 = sin(x + y)
arguments(expr4)             # returns collection containing (x + y)
arguments(arguments(expr4)[1])  # returns collection containing x and y
```

See also: [`iscall`](@ref), [`operation`](@ref)
"""
function TermInterface.arguments(x::BSImpl.Type{T})::ROArgsT{T} where {T}
    @match x begin
        BSImpl.Const(_) => throw(ArgumentError("`Const` does not have arguments."))
        BSImpl.Sym(_) => throw(ArgumentError("`Sym` does not have arguments."))
        BSImpl.Term(; args) => ROArgsT{T}(args)
        BSImpl.AddMul(; coeff, dict, variant, args, shape, type) => begin
            isempty(args) || return ROArgsT{T}(args)
            @match variant begin
                AddMulVariant.ADD => begin
                    if !iszero(coeff)
                        push!(args, Const{T}(coeff))
                    end
                    for (k, v) in dict
                        newterm = @match k begin
                            BSImpl.AddMul(; dict = d2, variant = v2, type, shape, metadata) && if v2 == AddMulVariant.MUL end => begin
                                Mul{T}(v, d2; shape, type, metadata)
                            end
                            _ => Mul{T}(v, ACDict{T}(k => 1); shape, type)
                        end
                        push!(args, newterm)
                    end
                end
                AddMulVariant.MUL => begin
                    if !isone(coeff)
                        push!(args, Const{T}(coeff))
                    end
                    for (k, v) in dict
                        push!(args, k ^ v)
                    end
                end
            end
            return ROArgsT{T}(args)
        end
        BSImpl.Div(num, den) => ROArgsT{T}(ArgsT{T}((num, den)))
        BSImpl.ArrayOp(; output_idx, expr, reduce, term, ranges, shape, type, args) => begin
            if term === nothing
                isempty(args) || return ROArgsT{T}(args)
                push!(args, Const{T}(output_idx))
                push!(args, Const{T}(expr))
                push!(args, Const{T}(reduce))
                push!(args, Const{T}(term))
                push!(args, Const{T}(ranges))
                return ROArgsT{T}(args)
            elseif term isa BasicSymbolic{T}
                return arguments(term)
            end
        end
    end
end

"""
    $TYPEDSIGNATURES

Check if a symbolic expression `expr` represents a function call. Returns `true` if the 
expression is a composite expression with an operation and arguments, `false` otherwise.

This function is fundamental for traversing and analyzing symbolic expressions. In 
SymbolicUtils.jl, an expression is considered a "call" if it represents a function 
application (including operators like +, -, *, etc.).

# Examples
```julia
using SymbolicUtils
@variables x y

# Basic variables are not calls
iscall(x)           # false

# Function calls are calls  
expr = sin(x + y)
iscall(expr)        # true

# Arithmetic expressions are calls
iscall(x + y)       # true
iscall(x * y)       # true
```

See also: [`operation`](@ref), [`arguments`](@ref)
"""
function TermInterface.iscall(s::BSImpl.Type)
    !MData.isa_variant(s, BSImpl.Sym) && !MData.isa_variant(s, BSImpl.Const)
end

function TermInterface.maketerm(::Type{BasicSymbolic{TreeReal}}, f, args, metadata; @nospecialize(type = _promote_symtype(f, args)))
    sh = promote_shape(f, shape.(args)...)
    Term{TreeReal}(f, args; type, shape=sh, metadata=metadata)
end

function TermInterface.maketerm(::Type{BasicSymbolic{T}}, f, args, metadata; @nospecialize(type = _promote_symtype(f, args))) where {T}
    @nospecialize f
    args = unwrap_args(args)
    if f isa Symbol
        error("$f must not be a Symbol")
    elseif f === ArrayOp{T}
        return ArrayOp{T}(args...)::BasicSymbolic{T}
    elseif f === broadcast
        _f, _args = Iterators.peel(args)
        res = broadcast(unwrap_const(_f), _args...)
        if metadata !== nothing && iscall(res)
            @set! res.metadata = metadata
        end
        return res::BasicSymbolic{T}
    elseif f === getindex
        # This can't call `getindex` because that goes through `@cache`, which is unstable
        # and doesn't precompile.
        res = _getindex(T, unwrap_const.(args)...)
        if metadata !== nothing && iscall(res)
            @set! res.metadata = metadata
        end
        return res::BasicSymbolic{T}
    elseif f === array_literal
        sh = ShapeVecT()
        for dim in unwrap_const(args[1])
            push!(sh, 1:dim)
        end
        BSImpl.Term{T}(f, args; type, shape = sh)
    elseif _numeric_or_arrnumeric_type(type)
        if f === (+)
            res = add_worker(T, args)
            if metadata !== nothing && (isadd(res) || (isterm(res) && operation(res) == (+)))
                @set! res.metadata = metadata
            end
            return res
        elseif f === (-)
            if length(args) == 1
                res = mul_worker(T, (-1, args[1]))
            else
                res = add_worker(T, (args[1], -args[2]))
            end
            if metadata !== nothing && (isadd(res) || (isterm(res) && operation(res) == (+)))
                @set! res.metadata = metadata
            end
            return res
        elseif f === (*)
            res = mul_worker(T, args)
            if metadata !== nothing && (ismul(res) || (isterm(res) && operation(res) == (*)))
                @set! res.metadata = metadata
            end
            return res
        elseif f === (/)
            @assert length(args) == 2
            res = args[1] / args[2]
            if metadata !== nothing && isdiv(res)
                @set! res.metadata = metadata
            end
            return res
        elseif f === (^) && length(args) == 2
            res = args[1] ^ args[2]
            if metadata !== nothing && ispow(res)
                @set! res.metadata = metadata
            end
            return res
        else
            @goto FALLBACK
        end
    else
        @label FALLBACK
        sh = promote_shape(f, shape.(args)...)
        Term{T}(f, args; type, shape=sh, metadata=metadata)
    end
end

