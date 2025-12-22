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

# Formal syntax

Following is a semi-formal CFG of the syntax accepted by this macro:

```python
# any variable accepted by this macro must be a `var`.
# `var` can represent a quantity (`value`) or a function `(fn)`.
var = value | fn
# A `value` is represented as a name followed by a suffix
value = name suffix
# A `name` can be a valid Julia identifier
name = ident |
# Or it can be an interpolated variable, in which case `ident` is assumed to refer to
# a variable in the current scope of type `Symbol` containing the name of this variable.
# Note that in this case the created symbolic variable will be bound to a randomized
# Julia identifier.
       "\$" ident |
# Or it can be of the form `Foo.Bar.baz` referencing a value accessible as `Foo.Bar.baz`
# in the current scope.
       getproperty_literal
getproperty_literal = ident "." getproperty_literal | ident "." ident
# The `suffix` can be empty (no suffix) which defaults the type to `Number`
suffix = "" |
# or it can be a type annotation (setting the type of the prefix). The shape of the result
# is inferred from the type as best it can be. In particular, `Array{T, N}` is inferred
# to have shape `Unknown(N)`.
         "::" type |
# or it can be a shape annotation, which sets the shape to the one specified by `ranges`.
# The type defaults to `Array{Number, length(ranges)}`
         "[" ranges "]" |
# lastly, it can be a combined shape and type annotation. Here, the type annotation
# sets the `eltype` of the symbolic array.
         "[" ranges "]::" type
# `ranges` is either a single `range` or a single range followed by one or more `ranges`.
ranges = range | range "," ranges
# A `range` is simply two bounds separated by a colon, as standard Julia ranges work.
# The range must be non-empty. Each bound can be a literal integer or an identifier
# representing an integer in the current scope.
range = (int | ident) ":" (int | ident) |
# Alternatively, a range can be a Julia expression that evaluates to a range. All identifiers
# used in `expr` are assumed to exist in the current scope.
        expr |
# Alternatively, a range can be a Julia expression evaluating to an iterable of ranges,
# followed by the splat operator.
        expr "..."
# A function is represented by a function-call syntax `fncall` followed by the `suffix`
# above. The type and shape from `suffix` represent the type and shape of the value
# returned by the symbolic function.
fn = fncall suffix
# a function call is a call `head` followed by a parenthesized list of arguments.
fncall = head "(" args ")"
# A function call head can be a name, representing the name of the symbolic function.
head = ident |
# Alternatively, it can be a parenthesized type-annotated name, where the type annotation
# represents the intended supertype of the function. In other words, if this symbolic
# function were to be replaced by an "actual" function, the type-annotation constrains the
# type of the "actual" function.
       "(" ident "::" type ")"
# Arguments to a function is a list of one or more arguments
args = arg | arg "," args
# An argument can take the syntax of a variable (which means we can represent functions of
# functions of functions of...). The type of the variable constrains the type of the
# corresponding argument of the function. The name and shape information is discarded.
arg = var |
# Or an argument can be an unnamed type-annotation, which constrains the type without
# requiring a name.
      "::" type |
# Or an argument can be the identifier `..`, which is used as a stand-in for `Vararg{Any}`
      ".." |
# Or an argument can be a type-annotated `..`, representing `Vararg{type}`. Note that this
# and the previous version of `arg` can only be the last element in `args` due to Julia's
# `Tuple` semantics.
      "(..)::" type |
# Or an argument can be a Julia expression followed by a splat operator. This assumes the
# expression evaluates to an iterable of symbolic variables whose `symtype` should be used
# as the argument types. Note that `expr` may be evaluated multiple times in the macro
# expansion.
      expr "..."
```
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
        nts = parse_variable(x)
        push!(ntss, nts)
        res = sym_from_parse_result(nts, _vartype)
        if nts[:isruntime]
            varname = Symbol(nts[:name])
        else
            varname = esc(nts[:name])
        end
        res = :($varname = $res)
        push!(expr.args, res)
        push!(allofem.args, varname)
    end
    push!(expr.args, allofem)
    return expr
end

function syms_syntax_error(x)
    error("Incorrect @syms syntax $x. Try `@syms x::Real y::Complex g(a) f(::Real)::Real` for instance.")
end

const ParseDictT = Dict{Symbol, Any}

"""
    $TYPEDSIGNATURES

Return an `Expr` which constructs a `Sym` for the given parsed variable `result`. `vartype`
is the vartype of the variable to be constructed. `do_esc` controls whether this function
is responsible for `esc`ing necessary values, or the caller will manually sanitize and `esc`
the expression.
"""
function sym_from_parse_result(result::ParseDictT, vartype; do_esc = true)::Expr
    n, t, s = result[:name], result[:type], result[:shape]
    T = do_esc ? esc(t) : t
    s = do_esc ? esc(s) : s
    if result[:isruntime]::Bool
        varname = do_esc ? esc(n) : n
    else
        varname = Expr(:quote, n)
    end
    return :($Sym{$vartype}($(varname); type = $T, shape = $s))
end

"""
    $(TYPEDSIGNATURES)

Parse an `Expr` or `Symbol` representing a variable in the syntax of the `@syms` macro.
Returns a `$ParseDictT` with the following keys guaranteed to exist:

- `:name`: The name of the variable. `nothing` if not specified.
- `:type`: The type of the variable. `default_type` if not specified.
- `:shape`: The shape of the variable.
- `:isruntime`: Whether the name is a runtime value (comes from a `\$name` interpolation syntax).

This does not attempt to `eval` to interpret types. Values in the above keys are concrete
values when possible and `Expr`s when not.

If the variable is a function, it contains additional keys:

- `:head`: A `$ParseDictT` containing the name and type of the function.
- `:args`: A list of `$ParseDictT` corresponding to each argument of the function. If there
  is a single argument `..`, the only `$ParseDictT` in `:args` will only contain
  `:name => :..`. For arguments of the form `::T` (type annotation without a name) the
  name will be `nothing`.

Refer to the docstring for [`@syms`](@ref) for a description of the grammar accepted by
this function.
"""
Base.@nospecializeinfer function parse_variable(x; default_type = Number)::ParseDictT
    @nospecialize x
    x = unwrap(x)
    if x isa Symbol
        # just a symbol
        type = if x == :..
            Vararg{Any}
        else
            default_type
        end
        return ParseDictT(:name => x, :type => type, :shape => ShapeVecT(), :isruntime => false)
    elseif Meta.isexpr(x, :.)
        # just a symbol
        type = if x == :..
            Vararg{Any}
        else
            default_type
        end
        return ParseDictT(:name => x, :type => type, :shape => ShapeVecT(), :isruntime => true)
    elseif Meta.isexpr(x, :$)
        return ParseDictT(:name => x.args[1], :type => default_type, :shape => ShapeVecT(), :isruntime => true)
    elseif Meta.isexpr(x, :call)
        # a function
        head = x.args[1]
        args = x.args[2:end]
        result = ParseDictT()
        result[:head] = parse_variable(head; default_type = Nothing)
        fname = result[:head][:name]
        ftype = result[:head][:type]
        result[:args] = [parse_variable(arg; default_type) for arg in args]
        arg_types = [arg[:type] for arg in result[:args]]
        signature = :(Tuple{$(arg_types...)})
        result[:name] = fname
        result[:type] = :($FnType{$signature, $default_type, $ftype})
        result[:shape] = ShapeVecT()
        result[:isruntime] = result[:head][:isruntime]
        return result
    elseif Meta.isexpr(x, :ref)
        result = parse_variable(x.args[1]; default_type)
        shape = Expr(:call, ShapeVecT, Expr(:tuple, x.args[2:end]...))
        ntype = result[:type]
        ndim = length(x.args) - 1
        if ndim > 0 && Meta.isexpr(x.args[end], :...)
            ndim = :($(ndim - 1) + length($(x.args[end].args[1])))
        end
        if Meta.isexpr(ntype, :curly) && ntype.args[1] === FnType
            ntype.args[3] = :($Array{$(ntype.args[3]), $(ndim)})
        else
            ntype = :($Array{$ntype, $(ndim)})
        end
        result[:type] = ntype
        result[:shape] = shape
        return result
    elseif Meta.isexpr(x, :(::))
        if length(x.args) == 1
            type = x.args[1]
            shape = shape_from_type(type, ShapeVecT())
            return ParseDictT(:name => nothing, :type => x.args[1], :shape => shape)
        end
        head, type = x.args
        result = parse_variable(head; default_type)
        shape = shape_from_type(type, result[:shape])
        ntype = result[:type]
        if Meta.isexpr(ntype, :curly) && ntype.args[1] === FnType
            if Meta.isexpr(ntype.args[3], :curly) && ntype.args[3].args[1] === Array
                ntype.args[3].args[2] = type
            else
                ntype.args[3] = type
            end
        elseif Meta.isexpr(ntype, :curly) && ntype.args[1] === Array
            ntype.args[2] = type
        elseif head == :..
            ntype = :(Vararg{$type})
        else
            ntype = type
        end
        result[:type] = ntype
        result[:shape] = shape
        return result
    elseif Meta.isexpr(x, :...)
        result = ParseDictT()
        result[:name] = x
        result[:type] = :($symtype.($(x.args[1]))...)
        result[:shape] = nothing
        result[:isruntime] = false
        return result
    elseif x isa BasicSymbolic{SymReal}
        result = ParseDictT()
        result[:name] = SymbolicIndexingInterface.getname(x)
        result[:type] = symtype(x)
        result[:shape] = (@__MODULE__).shape(x)
        result[:isruntime] = false
        return result
    elseif x isa BasicSymbolic{SafeReal}
        result = ParseDictT()
        result[:name] = SymbolicIndexingInterface.getname(x)
        result[:type] = symtype(x)
        result[:shape] = (@__MODULE__).shape(x)
        result[:isruntime] = false
        return result
    elseif x isa BasicSymbolic{TreeReal}
        result = ParseDictT()
        result[:name] = SymbolicIndexingInterface.getname(x)
        result[:type] = symtype(x)
        result[:shape] = (@__MODULE__).shape(x)
        result[:isruntime] = false
        return result
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
        return Unknown(-1)
    elseif Meta.isexpr(type, :curly)
        if type.args[1] == :Vector
            return Unknown(1)
        elseif type.args[1] == :Matrix
            return Unknown(2)
        elseif type.args[1] == :Array
            return Expr(:call, Unknown, length(type.args) == 3 ? type.args[3] : -1)
        else
            return default
        end
    else
        return default
    end
end

function shape_from_type(t::Type, default)
    if t <: AbstractArray
        if hasmethod(ndims, Tuple{t})
            Unknown(ndims(t))
        else
            Unknown(-1)
        end
    else
        default
    end
end

"""
    BS[...]
    BS{T}[...]

`BS` is a utility defined in SymbolicUtils for constructing arrays of symbolics. Similar to
how `T[...]` creates an `Array` of eltype `T`, `BS[...]` creates an array of eltype
`BasicSymbolic{T}`. To infer the [`vartype`](@ref) of the result, at least one of the values
in `...` must be a symbolic. `BS{T}[...]` can be used to explicitly specify the `vartype`.
"""
struct BS{T} end

@inline vartype_from_literal(::BasicSymbolic{T}, xs...) where {T} = T
@inline vartype_from_literal(_, xs...) = vartype_from_literal(xs...)
@inline function vartype_from_literal()
    error("Cannot infer `vartype` from array literal - use `BS{T}[...]` instead of `BS[...]`")
end

@inline function Base.getindex(::Type{BS}, xs...)
    BasicSymbolic{vartype_from_literal(xs...)}[xs...]
end
@inline function Base.getindex(::Type{BS{T}}, xs...) where {T}
    BasicSymbolic{T}[xs...]
end
@inline function Base.typed_vcat(::Type{BS}, xs...)
    Base.typed_vcat(BasicSymbolic{vartype_from_literal(xs...)}, xs...)
end
@inline function Base.typed_vcat(::Type{BS{T}}, xs...) where {T}
    Base.typed_vcat(BasicSymbolic{T}, xs...)
end
@inline function Base.typed_vcat(::Type{BS}, xs::Number...)
    Base.typed_vcat(BasicSymbolic{vartype_from_literal(xs...)}, xs...)
end
@inline function Base.typed_vcat(::Type{BS{T}}, xs::Number...) where {T}
    Base.typed_vcat(BasicSymbolic{T}, xs...)
end
@inline function Base.typed_hcat(::Type{BS}, xs...)
    Base.typed_hcat(BasicSymbolic{vartype_from_literal(xs...)}, xs...)
end
@inline function Base.typed_hcat(::Type{BS{T}}, xs...) where {T}
    Base.typed_hcat(BasicSymbolic{T}, xs...)
end
@inline function Base.typed_hcat(::Type{BS}, xs::Number...)
    Base.typed_hcat(BasicSymbolic{vartype_from_literal(xs...)}, xs...)
end
@inline function Base.typed_hcat(::Type{BS{T}}, xs::Number...) where {T}
    Base.typed_hcat(BasicSymbolic{T}, xs...)
end
@inline function Base.typed_hvcat(::Type{BS}, dims::Base.Dims, xs...)
    Base.typed_hvcat(BasicSymbolic{vartype_from_literal(xs...)}, dims, xs...)
end
@inline function Base.typed_hvcat(::Type{BS{T}}, dims::Base.Dims, xs...) where {T}
    Base.typed_hvcat(BasicSymbolic{T}, dims, xs...)
end
@inline function Base.typed_hvcat(::Type{BS}, dims::Base.Dims, xs::Number...)
    Base.typed_hvcat(BasicSymbolic{vartype_from_literal(xs...)}, dims, xs::Number...)
end
@inline function Base.typed_hvcat(::Type{BS{T}}, dims::Base.Dims, xs::Number...) where {T}
    Base.typed_hvcat(BasicSymbolic{T}, dims, xs...)
end
@inline function Base.typed_hvncat(::Type{BS}, dims::Base.Dims, rf::Bool, xs...)
    Base.typed_hvncat(BasicSymbolic{vartype_from_literal(xs...)}, dims, rf, xs...)
end
@inline function Base.typed_hvncat(::Type{BS{T}}, dims::Base.Dims, rf::Bool, xs...) where {T}
    Base.typed_hvncat(BasicSymbolic{T}, dims, rf, xs...)
end
@inline function Base.typed_hvncat(::Type{BS}, dim::Int, xs...)
    Base.typed_hvncat(BasicSymbolic{vartype_from_literal(xs...)}, dim, xs...)
end
@inline function Base.typed_hvncat(::Type{BS{T}}, dim::Int, xs...) where {T}
    Base.typed_hvncat(BasicSymbolic{T}, dim, xs...)
end

