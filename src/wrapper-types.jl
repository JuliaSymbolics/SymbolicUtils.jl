export @symbolic_wrap, @wrapped
# Turn A{X} <: B{Int, X} into
#
# B{Int, X} where X
function set_where(subt, supert)
    if !(supert isa Expr && supert.head == :curly)
        return supert
    end

    Ss = []
    if subt isa Expr && subt.head == :curly
        Ss = subt.args[2:end]
    end

    Ts = intersect(supert.args[2:end], Ss)
    Expr(:where, supert, Ts...)
end

getname(x::Symbol) = x

function getname(x::Expr)
    @assert x.head == :curly
    return x.args[1]
end

macro symbolic_wrap(expr)
    @assert expr isa Expr && expr.head == :struct
    @assert expr.args[2].head == :(<:)
    sig = expr.args[2]
    T = getname(sig.args[1])
    supertype = set_where(sig.args[1], sig.args[2])

    quote
        $expr

        SymbolicUtils.has_symwrapper(::Type{<:$supertype}) = true
        SymbolicUtils.wrapper_type(::Type{<:$supertype}) = $T
        SymbolicUtils.wraps_type(::Type{$T}) = $supertype
    end |> esc
end

unwrap(x) = x
function wrapper_type end
function wraps_type end

has_symwrapper(::Type) = false
#=
@symbolic_wrap Num <: Real
@symbolic_wrap IntLike <: Integer

@wrapped function foo(x::Integer, y::Real, z)
    <expr> # expr can do istree etc!
end

function _foo(x, y, z)
    res = <expr>
end

foo(x::Symbolic{<:Integer}, y::Symbolic{<:Real}, z) = _foo(x, y, z)
foo(x::IntLike, y::SymUnion{Real}, z) = wrap(_foo(unwrap(x), unwrap(y), z))
foo(x::SymUnion{Integer}, y::Num, z) = wrap(_foo(unwrap(x), unwrap(y), z))
=#

function wrap_func_expr(mod, expr)
    @assert expr.head == :function || (expr.head == :(=) &&
                                       expr.args[1] isa Expr &&
                                       expr.args[1].head == :call)

    sig = expr.args[1]
    body = expr.args[2]

    fname = sig.args[1]
    args = sig.args[2:end]
    names = map(args) do arg
        if arg isa Expr && arg.head == :(::)
            arg.args[1]
        else
            arg
        end
    end

    types = map(args) do arg
        if arg isa Expr && arg.head == :(::)
            T = Base.eval(mod, arg.args[2])
            has_symwrapper(T) ? (T, :(SymbolicUtils.Symbolic{<:$T}), wrapper_type(T))  : (T,)
        else
            (Any,)
        end
    end

    # TODO: maybe don't drop first lol
    methods = map(Iterators.drop(Iterators.product(types...), 1)) do Ts
        method_args = map(names, Ts) do n, T
            :($n::$T)
        end

        :(function $fname($(method_args...))
            $body
        end)
    end

    quote
        $(methods...)
    end |> esc
end

macro wrapped(expr)
    wrap_func_expr(__module__, expr)
end
