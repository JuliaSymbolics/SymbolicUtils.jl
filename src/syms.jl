"""
    @syms <lhs_expr>[::T1] <lhs_expr>[::T2]...

For instance:

    @syms foo::Real bar baz(x, y::Real)::Complex

Create one or more variables. `<lhs_expr>` can be just a symbol in which case
it will be the name of the variable, or a function call in which case a function-like
variable which has the same name as the function being called. The Sym type, or
in the case of a function-like Sym, the output type of calling the function
can be set using the `::T` syntax.

# Examples:

- `@syms foo bar::Real baz::Int` will create
variable `foo` of symtype `Number` (the default), `bar` of symtype `Real`
and `baz` of symtype `Int`
- `@syms f(x) g(y::Real, x)::Int h(a::Int, f(b))` creates 1-arg `f` 2-arg `g`
and 2 arg `h`. The second argument to `h` must be a one argument function-like
variable. So, `h(1, g)` will fail and `h(1, f)` will work.
"""
macro syms(xs...)
    isempty(xs) && return ()
    _vartype = SymReal
    if Meta.isexpr(xs[end], :(=))
        x = xs[end]
        key, val = x.args
        @assert key == :vartype
        if val == :SymReal
            _vartype = SymReal
        elseif val == :SafeReal
            _vartype = SafeReal
        elseif val == :TreeReal
            _vartype = TreeReal
        else
            error("Invalid vartype $val")
        end
        xs = Base.front(xs)
    end
    expr = Expr(:block)
    allofem = Expr(:tuple)
    ntss = []
    for x in xs
        nts = _name_type_shape(x)
        push!(ntss, nts)
        n, t, s = nts.name, nts.type, nts.shape
        T = esc(t)
        s = esc(s)
        res = :($(esc(n)) = $Sym{$_vartype}($(Expr(:quote, n)); type = $T, shape = $s))
        push!(expr.args, res)
        push!(allofem.args, esc(n))
    end
    push!(expr.args, allofem)
    return expr
end

function syms_syntax_error(x)
    error("Incorrect @syms syntax $x. Try `@syms x::Real y::Complex g(a) f(::Real)::Real` for instance.")
end

Base.@nospecializeinfer function _name_type_shape(x)
    @nospecialize x
    if x isa Symbol
        # just a symbol
        return (; name = x, type = Number, shape = ShapeVecT())
    elseif Meta.isexpr(x, :call)
        # a function
        head = x.args[1]
        args = x.args[2:end]
        if head isa Expr
            head_nts = _name_type_shape(head)
            fname = head_nts.name
            ftype = head_nts.type
        else
            fname = head
            ftype = Nothing
        end
        if length(args) == 1 && args[1] == :..
            signature = Tuple
        else
            arg_types = map(arg -> _name_type_shape(arg).type, args)
            signature = :(Tuple{$(arg_types...)})
        end
        return (; name = fname, type = :($FnType{$signature, Number, $ftype}), shape = ShapeVecT())
    elseif Meta.isexpr(x, :ref)
        nts = _name_type_shape(x.args[1])
        shape = Expr(:call, ShapeVecT, Expr(:tuple, x.args[2:end]...))
        ntype = nts.type
        if Meta.isexpr(ntype, :curly) && ntype.args[1] === FnType
            ntype.args[3] = :($Array{$(ntype.args[2]), $(length(x.args) - 1)})
        else
            ntype = :($Array{$ntype, $(length(x.args) - 1)})
        end
        return (name = nts.name, type = ntype, shape = shape)
    elseif Meta.isexpr(x, :(::))
        if length(x.args) == 1
            type = x.args[1]
            shape = shape_from_type(type, ShapeVecT())
            return (; name = nothing, type = x.args[1], shape = shape)
        end
        head, type = x.args
        nts = _name_type_shape(head)
        shape = shape_from_type(type, nts.shape)
        ntype = nts.type
        if Meta.isexpr(ntype, :curly) && ntype.args[1] === FnType
            if Meta.isexpr(ntype.args[3], :curly) && ntype.args[3].args[1] === Array
                ntype.args[3].args[2] = type
            else
                ntype.args[3] = type
            end
        elseif Meta.isexpr(ntype, :curly) && ntype.args[1] === Array
            ntype.args[2] = type
        else
            ntype = type
        end
        return (name = nts.name, type = ntype, shape = shape)
    else
        syms_syntax_error(x)
    end
end

function shape_from_type(type::Union{Expr, Symbol}, default)
    if type == :Vector
        return Unknown(1)
    elseif type == :Matrix
        return Unknown(2)
    elseif type == :Array
        return Unknown(0)
    elseif Meta.isexpr(type, :curly)
        if type.args[1] == :Vector
            return Unknown(1)
        elseif type.args[1] == :Matrix
            return Unknown(2)
        elseif type.args[1] == :Array
            return Expr(:call, Unknown, length(type.args) == 3 ? type.args[3] : 0)
        else
            return default
        end
    else
        return default
    end
end
