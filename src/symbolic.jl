export @vars, term, @fun, showraw

Base.:(==)(a::Symbolic, b::Symbolic) = a === b || isequal(a,b)

#### Variables

"""
    Variable(name[, domain=Number])

A named variable with an optional domain.
domain defaults to number.
"""
struct Variable{T} <: Symbolic{T}
    name::Symbol
    type::Type{T}
end
Variable(x) = Variable(x, Number)
symtype(v::Variable) = v.type
Base.nameof(v::Variable) = v.name
Base.:(==)(a::Variable, b::Variable) = a === b
Base.:(==)(::Variable, ::Symbolic) = false
Base.:(==)(::Symbolic, ::Variable) = false

Base.isequal(v1::Variable, v2::Variable) = isequal(v1.name, v2.name)
Base.show(io::IO, v::Variable) = print(io, v.name)

function vars_syntax_error()
    error("Incorrect @vars syntax. Try `@vars x::Real y::Complex` for instance.")
end

function _name_type(x)
    if x isa Symbol
        return x, Number
    elseif x isa Expr && x.head === :(::)
        return x.args[1:2]
    else
        vars_syntax_error()
    end
end

macro vars(xs...)
    defs = map(xs) do x
        n, t = _name_type(x)
        :($(esc(n)) = Variable($(Expr(:quote, n)), $(esc(t))))
    end

    Expr(:block, defs...,
         :(tuple($(map(esc∘first∘_name_type, xs)...))))
end


#### Terms

struct Term{T} <: Symbolic{T}
    f::Any
    type::Type{T}
    arguments::Any
end

operation(x::Term) = x.f
symtype(x::Term)   = x.type
arguments(x::Term) = x.arguments

function Base.isequal(t1::Term, t2::Term)
    a1 = arguments(t1)
    a2 = arguments(t2)
    isequal(operation(t1), operation(t2)) && length(a1) == length(a2) &&
        all(isequal(l,r) for (l, r) in zip(a1,a2))
end

function term(f, args...; type = nothing)
    if type === nothing
        t = promote_symtype(f, map(symtype, args)...)
    else
        t = type
    end

    Term(f, t, [args...])
end

const show_simplified = Ref(true)
function Base.show(io::IOContext, t::Term)
    if get(io, :simplify, show_simplified[])
        s = simplify(t)
        color = isequal(s, t) ? :white : :yellow
        Base.show(IOContext(io, :simplify=>false, :withcolor=>color), s)
    else
        f = operation(t)
        fname = nameof(f)
        binary = fname in [:+, :-, :*, :/, :^]
        color = get(io, :withcolor, :white)
        binary && Base.printstyled(io, "(",color=color)
        Base.printstyled(io, Expr(:call, fname, arguments(t)...), color=color)
        binary && Base.printstyled(io, ")", color=color)
    end
end

showraw(io, t) = Base.show(IOContext(stdout, :simplify=>false), t)
showraw(t) = showraw(stdout, t)

#### Literal functions

# Maybe don't even need a new type, can just use Variable{FnType}
struct FnType{X<:Tuple,Y} end

fun(f,X=Tuple{Real},Y=Real) = Variable(f,FnType{X,Y})

function (f::Variable{<:FnType{X,Y}})(args...) where {X,Y}
    nrequired = fieldcount(X)
    ngiven    = nfields(args)

    if nrequired !== ngiven
        error("$f takes $nrequired arguments; $ngiven arguments given")
    end

    for i in 1:ngiven
        t = X.parameters[i]
        if !(symtype(args[i]) <: t)
            error("Argument to $f at position $i must be of symbolic type $t")
        end
    end
    term(f, args...; type = Y)
end

function (f::Variable)(args...)
    error("Variable $f of type $F are not callable. " *
          "Use @fun $f to create it as a callable. " *
          "See ?@fun for more options")
end

macro fun(name::Symbol)
    :(@fun $name(::$Number)) |> esc
end

macro fun(expr::Expr)
    if expr.head == :(::)
        fexpr       = expr.args[1]
        output_type = expr.args[2]
    elseif expr.head == :call
        fexpr       = expr
        output_type = Number
    else
        error("Not a @fun syntax. Try `@fun f(::Number, ::Number)::Number`, for instance.")
    end

    fname = fexpr.args[1]
    input_types = map(fexpr.args[2:end]) do arg
        if arg isa Expr && arg.head == :(::)
            arg.args[end]
        elseif arg isa Symbol
            Number
        end
    end

    rhs = Expr(:call,
               fun,
               Expr(:quote, fname),
               :(Tuple{$(input_types...)}) |> esc,
               output_type |> esc,
              )
    :($(esc(fname)) = $rhs)
end

function Base.show(io::IO, f::Variable{<:FnType{X,Y}}) where {X,Y}
    print(io, f.name)
    argrepr = join(map(t->"::"*string(t), X.parameters), ", ")
    print(io, "(", argrepr, ")")
    print(io, "::", Y)
end
