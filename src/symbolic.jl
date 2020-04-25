#--------------------
#--------------------
#### Symbolic
#--------------------
abstract type Symbolic{T} end

### Interface to be defined for `simplify` to work:

"""
    istree(x::T)

Check if `x` represents an expression tree. If returns true,
it will be assumed that `operation(::T)` and `arguments(::T)`
methods are defined. Definining these three should allow use
of `simplify` on custom types. Optionally `symtype(x)` can be
defined to return the expected type of the symbolic expression.
"""
istree(x) = false

"""
    operation(x::T)

Returns the operation (a function object) performed by an expression
tree. Called only if `istree(::T)` is true. Part of the API required
for `simplify` to work. Other required methods are `arguments` and `istree`
"""
function operation end

"""
    arguments(x::T)

Returns the arguments (a `Vector`) for an expression tree.
Called only if `istree(x)` is `true`. Part of the API required
for `simplify` to work. Other required methods are `operation` and `istree`
"""
function arguments end

"""
    symtype(x)

The supposed type of values in the domain of x. Tracing tools can use this type to
pick the right method to run or analyse code.

This defaults to `typeof(x)` if `x` is numeric, or `Any` otherwise.
For the types defined in this package, namely `T<:Symbolic{S}` it is `S`.

Define this for your symbolic types if you want `simplify` to apply rules
specific to numbers (such as commutativity of multiplication). Or such
rules that may be implemented in the future.
"""
function symtype end

symtype(x::Number) = typeof(x)

symtype(x) = Any

symtype(::Symbolic{T}) where {T} = T

### End of interface

"""
    to_symbolic(x)

Convert `x` to a `Symbolic` type, using the `istree`, `operation`, `arguments`,
and optionally `symtype` if available.
"""
to_symbolic(x::Symbolic) = x

function to_symbolic(x)
    if !istree(x)
        return x
    end

    op = to_symbolic(operation(x))

    if symtype(x) === Any
        Term(op, map(to_symbolic, arguments(x)))
    else
        Term{symtype(x)}(op, map(to_symbolic, arguments(x)))
    end
end

Base.one( s::Symbolic) = one( symtype(s))

Base.zero(s::Symbolic) = zero(symtype(s))

@noinline function promote_symtype(f, xs...)
    error("promote_symtype($f, $(join(xs, ", "))) not defined")
end



Base.:(==)(a::Symbolic, b::Symbolic) = a === b || isequal(a,b)

#--------------------
#--------------------
#### Variables
#--------------------
"""
    Variable{T}(name::Symbol)

A named variable of type `T`. Type `T` can be `FnType{X,Y}` which
means the variable is a function with the type signature X -> Y where
`X` is a tuple type of arguments and `Y` is any type.
"""
struct Variable{T} <: Symbolic{T}
    name::Symbol
end

Variable(x) = Variable{Number}(x)

Base.nameof(v::Variable) = v.name

Base.:(==)(a::Variable, b::Variable) = a === b

Base.:(==)(::Variable, ::Symbolic) = false

Base.:(==)(::Symbolic, ::Variable) = false

Base.isequal(v1::Variable, v2::Variable) = isequal(v1.name, v2.name)

Base.show(io::IO, v::Variable) = print(io, v.name)

#---------------------------
#---------------------------
#### Function-like variables
#---------------------------

# Maybe don't even need a new type, can just use Variable{FnType}
struct FnType{X<:Tuple,Y} end

fun(f,X=Tuple{Real},Y=Real) = Variable{FnType{X,Y}}(f)

function (f::Variable{<:FnType{X,Y}})(args...) where {X,Y}
    term(f, args...)
end

function (f::Variable)(args...)
    error("Variable $f of type $F are not callable. " *
          "Use @vars $f(var1, var2,...) to create it as a callable. " *
          "See ?@fun for more options")
end

"""
`promote_symtype(f::Variable{FnType{X,Y}}, arg_symtypes...)`

The resultant type of applying variable `f` to arugments of symtype `arg_symtypes...`.
if the arguments are of the wrong type then this function will error.
"""
function promote_symtype(f::Variable{FnType{X,Y}}, args...) where {X, Y}
    nrequired = fieldcount(X)
    ngiven    = nfields(args)

    if nrequired !== ngiven
        error("$f takes $nrequired arguments; $ngiven arguments given")
    end

    for i in 1:ngiven
        t = X.parameters[i]
        if !(args[i] <: t)
            error("Argument to $f at position $i must be of symbolic type $t")
        end
    end
    return Y
end

"""
    @vars varname[::T]...

Create one or more variables `@vars foo bar::Real baz::Int` will create
variable `foo` of symtype `Number` (the default), `bar` of symtype `Real`
and `baz` of symtype `Int`
"""
macro vars(xs...)
    defs = map(xs) do x
        n, t = _name_type(x)
        :($(esc(n)) = Variable{$(esc(t))}($(Expr(:quote, n))))
    end

    Expr(:block, defs...,
         :(tuple($(map(x->esc(_name_type(x).name), xs)...))))
end

function vars_syntax_error()
    error("Incorrect @vars syntax. Try `@vars x::Real y::Complex g(a) f(::Real)::Real` for instance.")
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
            type = map(x->_name_type(x).type, lhs.args[2:end])
            return (name=lhs.args[1], type=:($FnType{Tuple{$(type...)}, $rhs}))
        else
            return (name=lhs, type=rhs)
        end
    elseif x isa Expr && x.head === :call
        return _name_type(:($x::Number))
    else
        vars_syntax_error()
    end
end

function Base.show(io::IO, f::Variable{<:FnType{X,Y}}) where {X,Y}
    print(io, f.name)
    argrepr = join(map(t->"::"*string(t), X.parameters), ", ")
    print(io, "(", argrepr, ")")
    print(io, "::", Y)
end

#--------------------
#--------------------
#### Terms
#--------------------
struct Term{T} <: Symbolic{T}
    f::Any
    arguments::Any
end

Term(f, args) = Term{rec_promote_symtype(f, map(symtype, args)...)}(f, args)

operation(x::Term) = x.f

arguments(x::Term) = x.arguments

function Base.isequal(t1::Term, t2::Term)
    a1 = arguments(t1)
    a2 = arguments(t2)

    isequal(operation(t1), operation(t2)) && length(a1) == length(a2) &&
        all(isequal(l,r) for (l, r) in zip(a1,a2))
end

function term(f, args...; type = nothing)
    if type === nothing
        T = rec_promote_symtype(f, symtype.(args)...)
    else
        T = type
    end
    Term{T}(f, [args...])
end

#--------------------
#--------------------
####  Pretty printing
#--------------------
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

showraw(io, t) = Base.show(IOContext(io, :simplify=>false), t)
showraw(t) = showraw(stdout, t)
