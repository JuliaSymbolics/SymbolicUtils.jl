export @vars, term, @fun

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
Base.:(==)(a::Variable, b::Variable) = a === b
Base.:(==)(::Variable, ::Symbolic) = false
Base.:(==)(::Symbolic, ::Variable) = false

Base.isequal(v1::Variable, v2::Variable) = isequal(v1.name, v2.name)
Base.show(io::IO, v::Variable) = print(io, v.name, "::", v.type)

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

function Base.show(io::IO, t::Term)
    f = operation(t)
    fname = nameof(f)
    binary = fname in [:+, :-, :*, :/]
    binary && Base.print(io, "(")
    Base.print(io, Expr(:call, fname, arguments(t)...))
    binary && Base.print(io, ")")
    Base.print(io, "::", symtype(t))
end


#### Literal functions

# Maybe don't even need a new type, can just use Variable{FnType}
struct FnType{X<:Tuple,Y} end
struct LiteralFunction{F} <: Symbolic{F}
    name::Symbol
    type::F
end

LiteralFunction(name, X,Y) = LiteralFunction(name, FnType{X,Y}())

Base.nameof(f::LiteralFunction) = f.name
Base.isequal(l1::LiteralFunction, l2::LiteralFunction) = isequal(nameof(f1), nameof(f2))

function (f::LiteralFunction)(args...)

    nrequired = fieldcount(f.input_type)
    ngiven    = nfields(args)

    if nrequired !== ngiven
        error("$f takes $nrequired arguments; $ngiven arguments given")
    end

    for i in 1:ngiven
        t = f.input_type.parameters[i]
        if !(symtype(args[i]) <: t)
            error("Argument to $f at position $i must be of symbolic type $t")
        end
    end
    term(f, args...; type = f.output_type)
end

macro fun(name::Symbol)
    :(@fun $name(::$Real)) |> esc
end

macro fun(expr::Expr)
    if expr.head == :(::)
        fexpr       = expr.args[1]
        output_type = expr.args[2]
    elseif expr.head == :call
        fexpr       = expr
        output_type = Real
    else
        error("Not a @fun syntax. Try `@fun f(::Real, ::Real)::Real`, for instance.")
    end

    fname = fexpr.args[1]
    input_types = map(fexpr.args[2:end]) do arg
        if arg isa Expr && arg.head == :(::)
            arg.args[end]
        elseif arg isa Symbol
            Real
        end
    end

    rhs = Expr(:call,
               LiteralFunction,
               Expr(:quote, fname),
               :(Tuple{$(input_types...)}) |> esc,
               output_type |> esc,
              )
    :($(esc(fname)) = $rhs)
end

function Base.show(io::IO, f::LiteralFunction)
    print(io, f.name)
    argrepr = join(map(t->"::"*string(t), f.input_type.parameters), ", ")
    print(io, "(", argrepr, ")")
    print(io, "::", f.output_type)
end
