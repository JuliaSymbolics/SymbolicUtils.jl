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

Base.isequal(s::Symbolic, x) = false
Base.isequal(x, s::Symbolic) = false
Base.isequal(x::Symbolic, y::Symbolic) = false

function metadata end

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

"""
    promote_symtype(f, Ts...)

The result of applying `f` to arguments of [`symtype`](#symtype) `Ts...`

```julia
julia> promote_symtype(+, Real, Real)
Real

julia> promote_symtype(+, Complex, Real)
Number

julia> @syms f(x)::Complex
(f(::Number)::Complex,)

julia> promote_symtype(f, Number)
Complex
```

When constructing [`Term`](#Term)s without an explicit symtype,
`promote_symtype` is used to figure out the symtype of the Term.
"""
promote_symtype(f, Ts...) = Any


#--------------------
#--------------------
#### Syms
#--------------------
"""
    Sym{T}(name::Symbol)

A named variable of type `T`. Type `T` can be `FnType{X,Y}` which
means the variable is a function with the type signature X -> Y where
`X` is a tuple type of arguments and `Y` is any type.
"""
struct Sym{T} <: Symbolic{T}
    name::Symbol
    metadata::Any
end

metadata(s::Sym) = s.metadata

const Variable = Sym # old name
Sym(x) = Sym{symtype(x)}(x)

Base.nameof(v::Sym) = v.name

Base.isequal(v1::Sym{T}, v2::Sym{T}) where {T} = v1 === v2

Base.show(io::IO, v::Sym) = print(io, v.name)

#---------------------------
#---------------------------
#### Function-like variables
#---------------------------

# Maybe don't even need a new type, can just use Sym{FnType}
struct FnType{X<:Tuple,Y} end

(f::Sym{<:FnType})(args...) = term(f, args...)

function (f::Sym)(args...)
    error("Sym $f is not callable. " *
          "Use @syms $f(var1, var2,...) to create it as a callable. " *
          "See ?@fun for more options")
end

"""
`promote_symtype(f::Sym{FnType{X,Y}}, arg_symtypes...)`

The output symtype of applying variable `f` to arugments of symtype `arg_symtypes...`.
if the arguments are of the wrong type then this function will error.
"""
function promote_symtype(f::Sym{FnType{X,Y}}, args...) where {X, Y}
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
and 2 arg `f`. The second argument to `h` must be a one argument function-like
variable. So, `h(1, g)` will fail and `h(1, f)` will work.
"""
macro syms(xs...)
    defs = map(xs) do x
        nt = _name_type(x)
        n, t = nt.name, nt.type
        m = get(nt, :metadata, nothing)
        :($(esc(n)) = Sym{$(esc(t))}($(Expr(:quote, n)), $m))
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
            type = map(x->_name_type(x).type, lhs.args[2:end])
            return (name=lhs.args[1], type=:($FnType{Tuple{$(type...)}, $rhs}))
        else
            return (name=lhs, type=rhs)
        end
    elseif x isa Expr && x.head === :ref
        ntype = _name_type(x.args[1]) # a::Number
        N = length(x.args)-1
        return (name=ntype.name,
                type=:(AbstractArray{$(ntype.type), $N}),
                metadata=:(ArrayShape{$(ntype.type), $N}(Base.Slice.(($(x.args[2:end]...),)))))
    elseif x isa Expr && x.head === :call
        return _name_type(:($x::Number))
    else
        syms_syntax_error()
    end
end

function Base.show(io::IO, f::Sym{<:FnType{X,Y}}) where {X,Y}
    print(io, f.name)
    argrepr = join(map(t->"::"*string(t), X.parameters), ", ")
    print(io, "(", argrepr, ")")
    print(io, "::", Y)
end

#--------------------
#--------------------
#### Terms
#--------------------
"""
    Term{T}(f, args::AbstractArray)

or
    Term(f, args::AbstractArray)

Symbolic expression representing the result of calling `f(args...)`.

- `operation(t::Term)` returns `f`
- `arguments(t::Term)` returns `args`
- `symtype(t::Term)` returns `T`

If `T` is not provided during construction, it is queried by calling
`SymbolicUtils.promote_symtype(f, map(symtype, args)...)`.

See [promote_symtype](#promote_symtype)
"""
struct Term{T} <: Symbolic{T}
    f::Any
    metadata::Any
    arguments::Any
end

function Term(f, metadata, args)
    Term{rec_promote_symtype(f, map(symtype, args)...)}(f, metadata, args)
end

Term{T}(f, args) where T = Term{T}(f, nothing, args)
Term(f, args) = Term(f, nothing, args)

operation(x::Term) = x.f

arguments(x::Term) = x.arguments

metadata(x::Term) = x.metadata

function Base.hash(t::Term{T}, salt::UInt) where {T}
    hash(arguments(t), hash(operation(t), hash(T, salt)))
end

function Base.isequal(t1::Term, t2::Term)
    t1 === t2 && return true
    a1 = arguments(t1)
    a2 = arguments(t2)

    isequal(operation(t1), operation(t2)) && length(a1) == length(a2) &&
        all(isequal(l,r) for (l, r) in zip(a1,a2))
end

function term(f, args...; type = nothing, meta = nothing)
    if type === nothing
        T = rec_promote_symtype(f, symtype.(args)...)
    else
        T = type
    end
    Term{T}(f, meta, [args...])
end

#--------------------
#--------------------
####  Pretty printing
#--------------------
const show_simplified = Ref(true)

function Base.show(io::IO, t::Term)
    if get(io, :simplify, show_simplified[])
        s = simplify(t)
        color = isequal(s, t) ? :white : :yellow

        Base.printstyled(IOContext(io, :simplify=>false, :withcolor=>color),
                         s, color=color)
    else
        f = operation(t)
        args = arguments(t)
        fname = nameof(f)
        binary = Base.isbinaryoperator(fname)
        color = get(io, :withcolor, :white)
        openparen = "("
        closeparen = "("
        sep = " $fname "
        if f === (^)
            sep = "$fname"
            closeparen = openparen = ""
        end

        if binary
            get(io, :paren, false) && Base.printstyled(io, openparen,color=color)
            for i = 1:length(args)
                length(args) == 1 && Base.printstyled(io, fname, color=color)

                args[i] isa Complex && Base.printstyled(io, "(",color=color)
                Base.printstyled(IOContext(io, :paren => true),
                                 args[i], color=color)
                args[i] isa Complex && Base.printstyled(io, ")",color=color)

                i != length(args) && Base.printstyled(io, sep, color=color)
            end
            get(io, :paren, false) && Base.printstyled(io, closeparen, color=color)
        else
            if f === getindex
                Base.printstyled(io, "$(args[1])[", color=color)
                for i=2:length(args)
                    if args[i] isa Base.Slice
                        val = args[i].indices
                    elseif args[i] isa Base.Colon
                        val = :(:)
                    else
                        val = args[i]
                    end
                    Base.printstyled(IOContext(io, :paren => false),
                                     val, color=color)
                    i != length(args) && Base.printstyled(io, ", ", color=color)
                end
                Base.printstyled(io, "]", color=color)
            else
                Base.printstyled(io, "$fname(", color=color)
                for i=1:length(args)
                    Base.printstyled(IOContext(io, :paren => false),
                                     args[i], color=color)
                    i != length(args) && Base.printstyled(io, ", ", color=color)
                end
                Base.printstyled(io, ")", color=color)
            end
        end
    end
    return nothing
end

showraw(io, t) = Base.show(IOContext(io, :simplify=>false), t)
showraw(t) = showraw(stdout, t)
