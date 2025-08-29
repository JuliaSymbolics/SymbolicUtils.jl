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
    defs = map(xs) do x
        nt = _name_type(x)
        n, t = nt.name, nt.type
        T = esc(t)
        :($(esc(n)) = Sym{$_vartype}($(Expr(:quote, n)); type = $T))
    end
    Expr(:block, defs...,
         :(tuple($(map(x->esc(_name_type(x).name), xs)...))))
end

function syms_syntax_error()
    error("Incorrect @syms syntax. Try `@syms x::Real y::Complex g(a) f(::Real)::Real` for instance.")
end

function _name_type(x)
    if x isa Symbol
        return (name=x, type=Number)
    elseif x isa Expr && x.head === :(::)
        if length(x.args) == 1
            return (name=nothing, type=x.args[1])
        end
        lhs, rhs = x.args[1:2]
        if lhs isa Expr && lhs.head === :call
            # e.g. f(::Real)::Unreal
            if lhs.args[1] isa Expr
                func_name_and_type = _name_type(lhs.args[1])
                name = func_name_and_type.name
                functype = func_name_and_type.type
            else
                name = lhs.args[1]
                functype = Nothing
            end
            type = map(x->_name_type(x).type, lhs.args[2:end])
            return (name=name, type=:($FnType{Tuple{$(type...)}, $rhs, $functype}))
        else
            return (name=lhs, type=rhs)
        end
    elseif x isa Expr && x.head === :ref
        ntype = _name_type(x.args[1]) # a::Number
        N = length(x.args)-1
        return (name=ntype.name,
                type=:(Array{$(ntype.type), $N}),
                array_metadata=:(Base.Slice.(($(x.args[2:end]...),))))
    elseif x isa Expr && x.head === :call
        return _name_type(:($x::Number))
    else
        syms_syntax_error()
    end
end

