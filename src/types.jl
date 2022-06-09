#--------------------
#--------------------
#### Symbolic
#--------------------
abstract type Symbolic{T} end

TermInterface.exprhead(x::Symbolic) = :call

TermInterface.symtype(x::Number) = typeof(x)
TermInterface.symtype(::Symbolic{T}) where {T} = T

TermInterface.metadata(s::Symbolic) = s.metadata
TermInterface.metadata(s::Symbolic, meta) = Setfield.@set! s.metadata = meta

function hasmetadata(s::Symbolic, ctx)
    metadata(s) isa AbstractDict && haskey(metadata(s), ctx)
end

function getmetadata(s::Symbolic, ctx)
    md = metadata(s)
    if md isa AbstractDict
        md[ctx]
    else
        throw(ArgumentError("$s does not have metadata for $ctx"))
    end
end

function getmetadata(s::Symbolic, ctx, default)
    md = metadata(s)
    md isa AbstractDict ? get(md, ctx, default) : default
end

# pirated for Setfield purposes:
Base.ImmutableDict(d::ImmutableDict{K,V}, x, y)  where {K, V} = ImmutableDict{K,V}(d, x, y)

assocmeta(d::Dict, ctx, val) = (d=copy(d); d[ctx] = val; d)
function assocmeta(d::Base.ImmutableDict, ctx, val)::ImmutableDict{DataType,Any}
    # optimizations
    # If using upto 3 contexts, things stay compact
    if isdefined(d, :parent)
        d.key === ctx && return @set d.value = val
        d1 = d.parent
        if isdefined(d1, :parent)
            d1.key === ctx && return @set d.parent.value = val
            d2 = d1.parent
            if isdefined(d2, :parent)
                d2.key === ctx && return @set d.parent.parent.value = val
            end
        end
    end
    Base.ImmutableDict{DataType, Any}(d, ctx, val)
end

function setmetadata(s::Symbolic, ctx::DataType, val)
    if s.metadata isa AbstractDict
        @set s.metadata = assocmeta(s.metadata, ctx, val)
    else
        # fresh Dict
        @set s.metadata = Base.ImmutableDict{DataType, Any}(ctx, val)
    end
end

Base.isequal(::Symbolic, x) = false
Base.isequal(x, ::Symbolic) = false
Base.isequal(::Symbolic, ::Symbolic) = false


### End of interface

### Metatheory.jl e-graph rewriting integration 

"""
    SymtypeAnalysis

This abstract type is used to identify the EGraph analysis 
that keeps track of symtype through an EGraph. This must 
be added to every EGraph that is used in SymbolicUtils.
"""
abstract type SymtypeAnalysis <: AbstractAnalysis end
_getsymtype(T::Type{<:Symbolic{X}}) where X = X
_getsymtype(T::Type{X}) where {X} = X
EGraphs.make(an::Type{SymtypeAnalysis}, g::EGraph, n::ENodeLiteral) = symtype(n.value)
EGraphs.make(an::Type{SymtypeAnalysis}, g::EGraph, n::ENodeTerm{T}) where {T} = _getsymtype(T)
EGraphs.join(an::Type{SymtypeAnalysis}, A, B) = Union{A, B}

# TODO JOIN egraph analysis
TermInterface.symtype(ec::EClass) = getdata(ec, SymtypeAnalysis, Any)

function to_symbolic(x)
    Base.depwarn("`to_symbolic(x)` is deprecated, define the interface for your " *
                 "symbolic structure using `istree(x)`, `operation(x)`, `arguments(x)` " *
                 "and `similarterm(::YourType, f, args, symtype)`", :to_symbolic, force=true)

    x
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

const NO_METADATA = nothing

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
struct Sym{T, M} <: Symbolic{T}
    name::Symbol
    metadata::M
end

issym(s::Sym) = true
Base.nameof(s::Sym) = s.name

ConstructionBase.constructorof(s::Type{<:Sym{T}}) where {T} = (n,m) -> Sym{T}(n, metadata=m)

function (::Type{Sym{T}})(name; metadata=NO_METADATA) where {T}
    Sym{T, typeof(metadata)}(name, metadata)
end

Base.hash(s::Sym, u::UInt) = hash(s.name, u)

function Base.isequal(a::Sym, b::Sym)
    symtype(a) !== symtype(b) && return false
    isequal(nameof(a), nameof(b))
end

Base.show(io::IO, v::Sym) = Base.show_unquoted(io, v.name)

#---------------------------
#---------------------------
#### Function-like variables
#---------------------------

# Maybe don't even need a new type, can just use Sym{FnType}
struct FnType{X<:Tuple,Y} end

(f::Symbolic{<:FnType})(args...) = Term{promote_symtype(f, symtype.(args)...)}(f, [args...])

function (f::Symbolic)(args...)
    error("Sym $f is not callable. " *
          "Use @syms $f(var1, var2,...) to create it as a callable.")
end

"""
    promote_symtype(f::Sym{FnType{X,Y}}, arg_symtypes...)

The output symtype of applying variable `f` to arugments of symtype `arg_symtypes...`.
if the arguments are of the wrong type then this function will error.
"""
function promote_symtype(f::Symbolic{FnType{X,Y}}, args...) where {X, Y}
    if X === Tuple
        return Y
    end

    # This is to handle `Tuple{T} where T`, so we cannot reliably query the type
    # parameters of the `Tuple` in `FnType`.
    t = Tuple{args...}
    if !(t <: X)
        error("$t is not a subtype of $X.")
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
and 2 arg `h`. The second argument to `h` must be a one argument function-like
variable. So, `h(1, g)` will fail and `h(1, f)` will work.
"""
macro syms(xs...)
    defs = map(xs) do x
        n, t = _name_type(x)
        :($(esc(n)) = Sym{$(esc(t))}($(Expr(:quote, n))))
        nt = _name_type(x)
        n, t = nt.name, nt.type
        :($(esc(n)) = Sym{$(esc(t))}($(Expr(:quote, n))))
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
                type=:(Array{$(ntype.type), $N}),
                array_metadata=:(Base.Slice.(($(x.args[2:end]...),))))
    elseif x isa Expr && x.head === :call
        return _name_type(:($x::Number))
    else
        syms_syntax_error()
    end
end

function Base.show(io::IO, f::Symbolic{<:FnType{X,Y}}) where {X,Y}
    print(io, nameof(f))
    # Use `Base.unwrap_unionall` to handle `Tuple{T} where T`. This is not the
    # best printing, but it's better than erroring.
    argrepr = join(map(t->"::"*string(t), Base.unwrap_unionall(X).parameters), ", ")
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
struct Term{T, M} <: Symbolic{T}
    f::Any
    arguments::Any
    metadata::M
    hash::Ref{UInt} # hash cache
end

function ConstructionBase.constructorof(s::Type{<:Term{T}}) where {T}
    function (f, args, meta, hash)
        Term{T, typeof(meta)}(f, args, meta, hash)
    end
end

function (::Type{Term{T}})(f, args; metadata=NO_METADATA) where {T}
    Term{T, typeof(metadata)}(f, args, metadata, Ref{UInt}(0))
end

TermInterface.istree(t::Type{<:Term}) = true

function Term(f, args; metadata=NO_METADATA)
    Term{_promote_symtype(f, args)}(f, args, metadata=metadata)
end

TermInterface.operation(x::Term) = getfield(x, :f)

TermInterface.arguments(x::Term) = getfield(x, :arguments)

function Base.isequal(t1::Term, t2::Term)
    t1 === t2 && return true
    symtype(t1) !== symtype(t2) && return false

    a1 = arguments(t1)
    a2 = arguments(t2)

    isequal(operation(t1), operation(t2)) &&
        length(a1) == length(a2) &&
        all(isequal(l,r) for (l, r) in zip(a1,a2))
end

## This is much faster than hash of an array of Any
hashvec(xs, z) = foldr(hash, xs, init=z)

function Base.hash(t::Term, salt::UInt)
    !iszero(salt) && return hash(hash(t, zero(UInt)), salt)
    h = t.hash[]
    !iszero(h) && return h
    op = operation(t)
    oph = op isa Function ? nameof(op) : op
    h′ = hashvec(arguments(t), hash(oph, salt))
    t.hash[] = h′
    return h′
end

isassociative(::Any) = false
isassociative(::Union{typeof(+),typeof(*)}) = true

_promote_symtype(f::Sym, args) = promote_symtype(f, map(symtype, args)...)
function _promote_symtype(f, args)
    if length(args) == 0
        promote_symtype(f)
    elseif length(args) == 1
        promote_symtype(f, symtype(args[1]))
    elseif length(args) == 2
        promote_symtype(f, symtype(args[1]), symtype(args[2]))
    elseif isassociative(f)
        mapfoldl(symtype, (x,y) -> promote_symtype(f, x, y), args)
    else
        promote_symtype(f, map(symtype, args)...)
    end
end

function term(f, args...; type = nothing)
    if type === nothing
        T = _promote_symtype(f, args)
    else
        T = type
    end
    Term{T}(f, [args...])
end

"""
    unflatten(t::Symbolic{T})
Binarizes `Term`s with n-ary operations
"""
function unflatten(t::Symbolic{T}) where{T}
    if istree(t)
        f = operation(t)
        if f == (+) || f == (*)   # TODO check out for other n-ary --> binary ops 
            a = arguments(t)
            return foldl((x,y) -> Term{T}(f, [x, y]), a)
        end
    end
    return t
end

unflatten(t) = t


"""
    similarterm(t, f, args, symtype; metadata=nothing)

Create a term that is similar in type to `t`. Extending this function allows packages
using their own expression types with SymbolicUtils to define how new terms should
be created. Note that `similarterm` may return an object that has a
different type than `t`, because `f` also influences the result.

## Arguments

- `t` the reference term to use to create similar terms
- `f` is the operation of the term
- `args` is the arguments
- The `symtype` of the resulting term. Best effort will be made to set the symtype of the
  resulting similar term to this type.
"""
TermInterface.similarterm(t::Type{<:Symbolic}, f, args; metadata=nothing, exprhead=:call) = 
    similarterm(t, f, args, _promote_symtype(f, args); metadata=metadata, exprhead=exprhead)

TermInterface.similarterm(t::Type{<:Symbolic}, f::Symbol, args; metadata=nothing, exprhead=:call) =
    TermInterface.similarterm(t, eval(f), args; metadata=metadata, exprhead=exprhead)

TermInterface.similarterm(t::Type{<:Term}, f, args, symtype; metadata=nothing, exprhead=:call) = 
    Term{_promote_symtype(f, args)}(f, args; metadata=metadata)

TermInterface.similarterm(t::Type{<:Term}, f::Symbol, args, symtype; metadata=nothing, exprhead=:call) = 
    Term{_promote_symtype(eval(f), args)}(eval(f), args; metadata=metadata)


#--------------------
#--------------------
####  Pretty printing
#--------------------
const show_simplified = Ref(false)

Base.show(io::IO, t::Term) = show_term(io, t)

isnegative(t::Real) = t < 0
function isnegative(t)
    if istree(t) && operation(t) === (*)
        coeff = first(arguments(t))
        return isnegative(coeff)
    end
    return false
end

setargs(t, args) = Term{symtype(t)}(operation(t), args)
cdrargs(args) = setargs(t, cdr(args))

print_arg(io, x::Union{Complex, Rational}; paren=true) = print(io, "(", x, ")")
isbinop(f) = istree(f) && !istree(operation(f)) && Base.isbinaryoperator(nameof(operation(f)))
function print_arg(io, x; paren=false)
    if paren && isbinop(x)
        print(io, "(", x, ")")
    else
        print(io, x)
    end
end
print_arg(io, s::String; paren=true) = show(io, s)
function print_arg(io, f, x)
    f !== (*) && return print_arg(io, x)
    if Base.isbinaryoperator(nameof(f))
        print_arg(io, x, paren=true)
    else
        print_arg(io, x)
    end
end

function remove_minus(t)
    !istree(t) && return -t
    @assert operation(t) == (*)
    args = arguments(t)
    @assert args[1] < 0
    [-args[1], args[2:end]...]
end

function show_add(io, args)
    negs = filter(isnegative, args)
    nnegs = filter(!isnegative, args)
    for (i, t) in enumerate(nnegs)
        i != 1 && print(io, " + ")
        print_arg(io, +,  t)
    end

    for (i, t) in enumerate(negs)
        if i==1 && isempty(nnegs)
            print_arg(io, -, t)
        else
            print(io, " - ")
            show_mul(io, remove_minus(t))
        end
    end
end

function show_pow(io, args)
    base, ex = args

    if base isa Real && base < 0
        print(io, "(")
        print_arg(io, base)
        print(io, ")")
    else
        print_arg(io, base, paren=true)
    end
    print(io, "^")
    print_arg(io, ex, paren=true)
end

function show_mul(io, args)
    length(args) == 1 && return print_arg(io, *, args[1])

    minus = args[1] isa Number && args[1] == -1
    unit = args[1] isa Number && args[1] == 1

    paren_scalar = (args[1] isa Complex && !_iszero(imag(args[1]))) ||
                   args[1] isa Rational ||
                   (args[1] isa Number && !isfinite(args[1]))

    nostar = minus || unit ||
            (!paren_scalar && args[1] isa Number && !(args[2] isa Number))

    for (i, t) in enumerate(args)
        if i != 1
            if i==2 && nostar
            else
                print(io, "*")
            end
        end
        if i == 1 && minus
            print(io, "-")
        elseif i == 1 && unit
        else
            print_arg(io, *, t)
        end
    end
end

function show_ref(io, f, args)
    x = args[1]
    idx = args[2:end]

    istree(x) && print(io, "(")
    print(io, x)
    istree(x) && print(io, ")")
    print(io, "[")
    for i=1:length(idx)
        print_arg(io, idx[i])
        i != length(idx) && print(io, ", ")
    end
    print(io, "]")
end

function show_call(io, f, args)
    fname = istree(f) ? Symbol(repr(f)) : nameof(f)
    binary = Base.isbinaryoperator(fname)
    if binary
        for (i, t) in enumerate(args)
            i != 1 && print(io, " $fname ")
            print_arg(io, t, paren=true)
        end
    else
        if f isa Sym
            Base.show_unquoted(io, nameof(f))
        else
            Base.show(io, f)
        end
        print(io, "(")
        for i=1:length(args)
            print(io, args[i])
            i != length(args) && print(io, ", ")
        end
        print(io, ")")
    end
end

function show_term(io::IO, t)
    if get(io, :simplify, show_simplified[])
        return print(IOContext(io, :simplify=>false), simplify(t))
    end

    f = operation(t)
    args = arguments(t)

    if f === (+)
        show_add(io, args)
    elseif f === (*)
        show_mul(io, args)
    elseif f === (^)
        show_pow(io, args)
    elseif f === (getindex)
        show_ref(io, f, args)
    else
        show_call(io, f, args)
    end

    return nothing
end

showraw(io, t) = Base.show(IOContext(io, :simplify=>false), t)
showraw(t) = showraw(stdout, t)


######   Add Mul and Pow


sdict(kv...) = Dict{Any, Number}(kv...)

const SN = Symbolic{<:Number}
# TODO Reviewme this is necessary for Metatheory.jl egraph rewriting
# integration. Constructors of `Add, Mul, Pow...` from Base (+, *, ^, ...) 
# Should now accepts EClasses as arguments. 
const SN_EC = Union{SN, EClass}

"""
    Add(T, coeff, dict::Dict)

Represents `coeff + (key1 * val1) + (key2 * val2) + ...`

where keys and values come from the dictionary (`dict`).
where `coeff` and the vals are `<:Number` and keys are symbolic.

- `operation(::Add)` -- returns `+`.
- `symtype(::Add)` -- returns `T`.
- `arguments(::Add)` -- returns a totally ordered vector of arguments. i.e.
  `[coeff, keyM*valM, keyN*valN...]`
"""
struct Add{X<:Number, T<:Number, D, M} <: Symbolic{X}
    coeff::T
    dict::D
    sorted_args_cache::Ref{Any}
    hash::Ref{UInt}
    metadata::M
end

function Add(T, coeff, dict; metadata=NO_METADATA)
    if isempty(dict)
        return coeff
    elseif _iszero(coeff) && length(dict) == 1
        k,v = first(dict)
        return _isone(v) ? k : Mul(T, makemul(v, k)...)
    end

    Add{T, typeof(coeff), typeof(dict), typeof(metadata)}(coeff, dict, Ref{Any}(nothing), Ref{UInt}(0), metadata)
end

TermInterface.symtype(a::Add{X}) where {X} = X

TermInterface.istree(a::Type{Add}) = true

TermInterface.operation(a::Add) = +

function TermInterface.unsorted_arguments(a::Add)
    args = [v*k for (k,v) in a.dict]
    iszero(a.coeff) ? args : vcat(a.coeff, args)
end

function TermInterface.arguments(a::Add)
    a.sorted_args_cache[] !== nothing && return a.sorted_args_cache[]
    args = sort!([v*k for (k,v) in a.dict], lt=<ₑ)
    a.sorted_args_cache[] = iszero(a.coeff) ? args : vcat(a.coeff, args)
end

Base.isequal(a::Add, b::Add) = a.coeff == b.coeff && isequal(a.dict, b.dict)

Base.show(io::IO, a::Add) = show_term(io, a)

function toterm(t::Add{T}) where T
    args = []
    for (k, coeff) in t.dict
        push!(args, coeff == 1 ? k : Term{T}(*, [coeff, k]))
    end
    Term{T}(+, args)
end

toterm(t) = t


"""
    makeadd(sign, coeff::Number, xs...)

Any Muls inside an Add should always have a coeff of 1
and the key (in Add) should instead be used to store the actual coefficient
"""
function makeadd(sign, coeff, xs...)
    d = sdict()
    for x in xs
        if x isa Add
            coeff += x.coeff
            _merge!(+, d, x.dict, filter=_iszero)
            continue
        end
        if x isa Number
            coeff += x
            continue
        end
        if x isa Mul
            k = Mul(symtype(x), 1, x.dict)
            v = sign * x.coeff + get(d, k, 0)
        else
            k = x
            v = sign + get(d, x, 0)
        end
        if iszero(v)
            delete!(d, k)
        else
            d[k] = v
        end
    end
    coeff, d
end

add_t(a::Number,b::Number) = promote_symtype(+, symtype(a), symtype(b))
add_t(a,b) = promote_symtype(+, symtype(a), symtype(b))
sub_t(a,b) = promote_symtype(-, symtype(a), symtype(b))
sub_t(a) = promote_symtype(-, symtype(a))

function +(a::SN_EC, b::SN_EC)
    if a isa Add
        coeff, dict = makeadd(1, 0, b)
        T = promote_symtype(+, symtype(a), symtype(b))
        return Add(add_t(a,b), a.coeff + coeff, _merge(+, a.dict, dict, filter=_iszero))
    elseif b isa Add
        return b + a
    end
    Add(add_t(a,b), makeadd(1, 0, a, b)...)
end

+(a::Number, b::SN_EC) = Add(add_t(a,b), makeadd(1, a, b)...)

+(a::SN_EC, b::Number) = Add(add_t(a,b), makeadd(1, b, a)...)

+(a::SN_EC) = a

+(a::Add, b::Add) = Add(add_t(a,b),
                        a.coeff + b.coeff,
                        _merge(+, a.dict, b.dict, filter=_iszero))

+(a::Number, b::Add) = iszero(a) ? b : Add(add_t(a,b), a + b.coeff, b.dict)

+(b::Add, a::Number) = iszero(a) ? b : Add(add_t(a,b), a + b.coeff, b.dict)

-(a::Add) = Add(sub_t(a), -a.coeff, mapvalues((_,v) -> -v, a.dict))

-(a::SN_EC) = Add(sub_t(a), makeadd(-1, 0, a)...)

-(a::Add, b::Add) = Add(sub_t(a,b),
                        a.coeff - b.coeff,
                        _merge(-, a.dict, b.dict, filter=_iszero))

-(a::SN_EC, b::SN_EC) = a + (-b)

-(a::Number, b::SN_EC) = a + (-b)

-(a::SN_EC, b::Number) = a + (-b)

"""
    Mul(T, coeff, dict)

Represents coeff * (key1 ^ val1) * (key2 ^ val2) * ....

where coeff is a <:Number and keys and values come from the dictionary (`dict`).
where `coeff` and the vals are `<:Number` and keys are symbolic.

- `symtype(::Mul)` -- returns `T`.
- `operation(::Mul)` -- returns `*`.
- `arguments(::Mul)` -- returns a totally ordered vector of arguments. i.e.
  `[coeff, keyM^valM, keyN^valN...]`
"""
struct Mul{X<:Number, T<:Number, D, M} <: Symbolic{X}
    coeff::T
    dict::D
    sorted_args_cache::Ref{Any}
    hash::Ref{UInt}
    metadata::M
end

for S in [Add, Mul]
    @eval function ConstructionBase.constructorof(s::Type{<:$S{T}}) where {T}
        function (coeff, dict, argscache, hash, m)
            $S{T,
                typeof(coeff),
                typeof(dict),
                typeof(m)}(coeff,
            dict,
            argscache,
            hash,
            m)
        end
    end
end

function Mul(T, a,b; metadata=NO_METADATA)
    isempty(b) && return a
    if _isone(a) && length(b) == 1
        pair = first(b)
        if _isone(last(pair)) # first value
            return first(pair)
        else
            return unstable_pow(first(pair), last(pair))
        end
    else
        Mul{T, typeof(a), typeof(b), typeof(metadata)}(a,b, Ref{Any}(nothing), Ref{UInt}(0), metadata)
    end
end

TermInterface.symtype(a::Mul{X}) where {X} = X

TermInterface.istree(a::Type{Mul}) = true

TermInterface.operation(a::Mul) = *

unstable_pow(a, b) = a isa Integer && b isa Integer ? (a//1) ^ b : a ^ b

function TermInterface.unsorted_arguments(a::Mul)
    args = [unstable_pow(k, v) for (k,v) in a.dict]
    isone(a.coeff) ? args : vcat(a.coeff, args)
end

function TermInterface.arguments(a::Mul)
    a.sorted_args_cache[] !== nothing && return a.sorted_args_cache[]
    args = sort!([unstable_pow(k, v) for (k,v) in a.dict], lt=<ₑ)
    a.sorted_args_cache[] = isone(a.coeff) ? args : vcat(a.coeff, args)
end

Base.isequal(a::Mul, b::Mul) = a.coeff == b.coeff && isequal(a.dict, b.dict)

Base.show(io::IO, a::Mul) = show_term(io, a)

function toterm(t::Mul{T}) where T
    args = []
    push!(args, t.coeff)
    for (k, deg) in t.dict
        push!(args, deg == 1 ? k : Term{T}(^, [k, deg]))
    end
    Term{T}(*, args)
end


function makemul(coeff, xs...; d=sdict())
    for x in xs
        if x isa Pow && x.exp isa Number
            d[x.base] = x.exp + get(d, x.base, 0)
        elseif x isa Number
            coeff *= x
        elseif x isa Mul
            coeff *= x.coeff
            _merge!(+, d, x.dict, filter=_iszero)
        else
            v = 1 + get(d, x, 0)
            if _iszero(v)
                delete!(d, x)
            else
                d[x] = v
            end
        end
    end
    (coeff, d)
end

mul_t(a,b) = promote_symtype(*, symtype(a), symtype(b))
mul_t(a) = promote_symtype(*, symtype(a))

*(a::SN_EC) = a

function *(a::SN_EC, b::SN_EC)
    # Always make sure Div wraps Mul
    if a isa Div && b isa Div
        Div(a.num * b.num, a.den * b.den)
    elseif a isa Div
        Div(a.num * b, a.den)
    elseif b isa Div
        Div(a * b.num, b.den)
    else
        Mul(mul_t(a,b), makemul(1, a, b)...)
    end
end

*(a::Mul, b::Mul) = Mul(mul_t(a, b),
                        a.coeff * b.coeff,
                        _merge(+, a.dict, b.dict, filter=_iszero))

function *(a::Number, b::SN_EC)
    if iszero(a)
        a
    elseif isone(a)
        b
    elseif b isa Div
        Div(a*b.num, b.den)
    elseif b isa Add
        # 2(a+b) -> 2a + 2b
        T = promote_symtype(+, typeof(a), symtype(b))
        Add(T, b.coeff * a, Dict(k=>v*a for (k, v) in b.dict))
    else
        Mul(mul_t(a, b), makemul(a, b)...)
    end
end

*(a::SN_EC, b::Number) = b * a

\(a::SN_EC, b::Union{Number, SN_EC}) = b / a

\(a::Number, b::SN_EC) = b / a

/(a::SN_EC, b::Number) = (b isa Integer ? 1//b : inv(b)) * a

//(a::Union{SN_EC, Number}, b::SN_EC) = a / b

//(a::SN_EC, b::T) where {T <: Number} = (one(T) // b) * a

"""
    Div(numerator_factors, denominator_factors, simplified=false)

"""
struct Div{T,N,D, M} <: Symbolic{T}
    num::N
    den::D
    simplified::Bool
    metadata::M
end

Base.hash(x::Div, u::UInt64) = hash(x.num, hash(x.den, u))
Base.isequal(x::Div, y::Div) = isequal(x.num, y.num) && isequal(x.den, y.den)

const Rat = Union{Rational, Integer}

ratcoeff(x) = false, NaN
ratcoeff(x::Rat) = true, x
ratcoeff(x::Mul) = ratcoeff(x.coeff)
ratio(x::Integer,y::Integer) = iszero(rem(x,y)) ? div(x,y) : x//y
ratio(x::Rat,y::Rat) = x//y
function maybe_intcoeff(x::Mul)
    x.coeff isa Rational && isone(x.coeff.den) ? Setfield.@set!(x.coeff = x.coeff.num) : x
end
maybe_intcoeff(x::Rational) = isone(x.den) ? x.num : x
maybe_intcoeff(x) = x

function (::Type{Div{T}})(n, d, simplified=false; metadata=nothing) where {T}
    if T<:Number && !(T<:SafeReal)
        n, d = quick_cancel(n, d)
    end
    _iszero(n) && return zero(typeof(n))
    _isone(d) && return n

    if n isa Div && d isa Div
        return Div{T}(n.num * d.den, n.den * d.num)
    elseif n isa Div
        return Div{T}(n.num, n.den * d)
    elseif d isa Div
        return Div{T}(n * d.den, d.num)
    end

    d isa Number && _isone(-d) && return -1 * n
    n isa Rat && d isa Rat && return n // d # maybe called by oblivious code in simplify

    # GCD coefficient upon construction
    rat, nc = ratcoeff(n)
    if rat
        rat, dc = ratcoeff(d)
        if rat
            g = gcd(nc, dc) * sign(dc) # make denominator positive
            invdc = ratio(1, g)
            n = maybe_intcoeff(invdc * n)
            d = maybe_intcoeff(invdc * d)
        end
    end

    Div{T, typeof(n), typeof(d), typeof(metadata)}(n, d, simplified, metadata)
end

function Div(n,d, simplified=false; kw...)
    Div{promote_symtype((/), symtype(n), symtype(d))}(n,d, simplified; kw...)
end

numerators(x) = istree(x) && operation(x) == (*) ? arguments(x) : [x]
numerators(d::Div) = numerators(d.num)

denominators(x) = [1]
denominators(d::Div) = numerators(d.den)

TermInterface.istree(d::Type{Div}) = true

TermInterface.operation(d::Div) = (/)

function TermInterface.arguments(d::Div)
    [d.num, d.den]
end

Base.show(io::IO, d::Div) = show_term(io, d)

function toterm(t::Div{T}) where T
    Term{T}(/, [t.num, t.den])
end

/(a::Union{SN_EC,Number}, b::SN_EC) = Div(a,b)

"""
    Pow(base, exp)

Represents `base^exp`, a lighter version of `Mul(1, Dict(base=>exp))`
"""
struct Pow{X, B, E, M} <: Symbolic{X}
    base::B
    exp::E
    metadata::M
end

function ConstructionBase.constructorof(::Type{<:Pow{X}}) where {X}
    (base, exp, m) ->
    Pow{promote_symtype(^, symtype(base), symtype(exp)), typeof(base), typeof(exp), typeof(m)}(base,exp,m)
end

function (::Type{<:Pow{T}})(a, b; metadata=NO_METADATA) where {T}
    _iszero(b) && return 1
    _isone(b) && return a
    Pow{T, typeof(a), typeof(b), typeof(metadata)}(a,b,metadata)
end
function Pow(a, b; metadata=NO_METADATA)
    Pow{promote_symtype(^, symtype(a), symtype(b))}(makepow(a, b)..., metadata=metadata)
end
TermInterface.symtype(a::Pow{X}) where {X} = X

TermInterface.istree(a::Type{Pow}) = true

TermInterface.operation(a::Pow) = ^

# Use `Union` to avoid promoting the base and exponent to the same type.
# For instance, if `a.base` is a multivariate polynomial and  `a.exp` is a number,
# we don't want to promote `a.exp` to a multivariate polynomial.
TermInterface.arguments(a::Pow) = Union{typeof(a.base), typeof(a.exp)}[a.base, a.exp]

Base.hash(p::Pow, u::UInt) = hash(p.exp, hash(p.base, u))

Base.isequal(p::Pow, b::Pow) = isequal(p.base, b.base) && isequal(p.exp, b.exp)

Base.show(io::IO, p::Pow) = show_term(io, p)

function toterm(t::Pow{T}) where T
    Term{T}(^, [t.base, t.exp])
end

function makepow(a, b)
    base = a
    exp = b
    if a isa Pow
        base = a.base
        exp = a.exp * b
    end
    return (base, exp)
end

^(a::SN_EC, b) = Pow(a, b)

^(a::SN_EC, b::SN_EC) = Pow(a, b)

^(a::Number, b::SN_EC) = Pow(a, b)

function ^(a::Mul, b::Number)
    coeff = unstable_pow(a.coeff, b)
    Mul(promote_symtype(^, symtype(a), symtype(b)),
        coeff, mapvalues((k, v) -> b*v, a.dict))
end

function *(a::Mul, b::Pow)
    if b.exp isa Number
        Mul(mul_t(a, b),
            a.coeff, _merge(+, a.dict, Base.ImmutableDict(b.base=>b.exp), filter=_iszero))
    else
        Mul(mul_t(a, b),
            a.coeff, _merge(+, a.dict, Base.ImmutableDict(b=>1), filter=_iszero))
    end
end

*(a::Pow, b::Mul) = b * a

function copy_similar(d, others)
    K = promote_type(keytype(d), keytype.(others)...)
    V = promote_type(valtype(d), valtype.(others)...)
    Dict{K, V}(d)
end

_merge(f, d, others...; filter=x->false) = _merge!(f, copy_similar(d, others), others...; filter=filter)
function _merge!(f, d, others...; filter=x->false)
    acc = d
    for other in others
        for (k, v) in other
            v = f(v)
            if haskey(acc, k)
                v = acc[k] + v
            end
            if filter(v)
                delete!(acc, k)
            else
                acc[k] = v
            end
        end
    end
    acc
end

function mapvalues(f, d1::AbstractDict)
    d = copy(d1)
    for (k, v) in d
        d[k] = f(k, v)
    end
    d
end

const NumericTerm = Union{Term{<:Number}, Mul{<:Number},
                          Add{<:Number}, Pow{<:Number}, Div{<:Number}}

function TermInterface.similarterm(t::Type{P}, f, args, symtype; metadata=nothing, exprhead=:call) where P<:NumericTerm
    T = symtype
    if T === nothing
        T = _promote_symtype(f, args)
    end
    if f === (+)
        Add(T, makeadd(1, 0, args...)...; metadata=metadata)
    elseif f == (*)
        Mul(T, makemul(1, args...)...; metadata=metadata)
    elseif f == (/)
        @assert length(args) == 2
        Div{T}(args...; metadata=metadata)
    elseif f == (^) && length(args) == 2
        Pow{T}(makepow(args...)...; metadata=metadata)
    else
        Term{T}(f, args; metadata=metadata)
    end
end

function Base.hash(t::Union{Add,Mul}, u::UInt64)
    !iszero(u) && return hash(hash(t, zero(UInt64)), u)
    h = t.hash[]
    !iszero(h) && return h
    hashoffset = t isa Add ? 0xaddaddaddaddadda : 0xaaaaaaaaaaaaaaaa
    h′= hash(hashoffset, hash(t.coeff, hash(t.dict, u)))
    t.hash[] = h′
    return h′
end

import AbstractTrees

struct TreePrint
    op
    x
end
AbstractTrees.children(x::Term) = arguments(x)
function AbstractTrees.children(x::Union{Add, Mul})
    children = Any[x.coeff]
    for (key, coeff) in pairs(x.dict)
        if coeff == 1
            push!(children, key)
        else
            push!(children, TreePrint(x isa Add ? (:*) : (:^), (key, coeff)))
        end
    end
    return children
end
AbstractTrees.children(x::Union{Pow}) = [x.base, x.exp]
AbstractTrees.children(x::TreePrint) = [x.x[1], x.x[2]]

print_tree(x; show_type=false, maxdepth=Inf, kw...) = print_tree(stdout, x; show_type=show_type, maxdepth=maxdepth, kw...)
function print_tree(_io::IO, x::Union{Term, Add, Mul, Pow, Div}; show_type=false, kw...)
    AbstractTrees.print_tree(_io, x; withinds=true, kw...) do io, y, inds
        if istree(y)
            print(io, operation(y))
        elseif y isa TreePrint
            print(io, "(", y.op, ")")
        else
            print(io, y)
        end
        if !(y isa TreePrint) && show_type
            print(io, " [", typeof(y), "]")
        end
    end
end

TermInterface.istree(t::Type{<:Sym}) = false
TermInterface.istree(t::Type{<:Symbolic}) = true

# Compat
isterm(s) = s isa Term
ismul(s) = s isa Mul
isadd(s) = s isa Add
ispow(s) = s isa Pow
isdiv(s) = s isa Div
const BasicSymbolic = Union{Sym, Term, Mul, Add, Pow, Div}
