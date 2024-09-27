const TIMER_OUTPUTS = true
const being_timed = Ref{Bool}(false)

if TIMER_OUTPUTS
    using TimerOutputs

    macro timer(name, expr)
        :(if being_timed[]
              @timeit $(esc(name)) $(esc(expr))
          else
              $(esc(expr))
          end)
    end

    macro iftimer(expr)
        esc(expr)
    end

else
    macro timer(name, expr)
        esc(expr)
    end

    macro iftimer(expr)
    end
end

using Base: ImmutableDict


pow(x,y) = y==0 ? 1 : y<0 ? inv(x)^(-y) : x^y
pow(x::Symbolic,y) = y==0 ? 1 : Base.:^(x,y)
pow(x, y::Symbolic) = Base.:^(x,y)
pow(x::Symbolic,y::Symbolic) = Base.:^(x,y)

# Simplification utilities
function has_trig_exp(term)
    !iscall(term) && return false
    fns = (sin, cos, tan, cot, sec, csc, exp, cosh, sinh)
    op = operation(term)

    if Base.@nany 9 i->fns[i] === op
        return true
    else
        return any(has_trig_exp, arguments(term))
    end
end

function fold(t)
    if iscall(t)
        tt = map(fold, arguments(t))
        if !any(x->x isa Symbolic, tt)
            # evaluate it
            return operation(t)(tt...)
        else
            return maketerm(typeof(t), operation(t), tt, metadata(t))
        end
    else
        return t
    end
end

### Predicates

sym_isa(::Type{T}) where {T} = @nospecialize(x) -> x isa T || symtype(x) <: T

function is_literal_number(x)
    if isconst(x)
        x = get_val(x)
    end
    x isa Number
end

# checking the type directly is faster than dynamic dispatch in type unstable code
_iszero(x) = x isa Number && iszero(x)
_isone(x) = x isa Number && isone(x)
_isinteger(x) = (x isa Number && isinteger(x)) || (x isa Symbolic && symtype(x) <: Integer)
_isreal(x) = (x isa Number && isreal(x)) || (x isa Symbolic && symtype(x) <: Real)

issortedₑ(args) = issorted(args, lt=<ₑ)
needs_sorting(f) = x -> is_operation(f)(x) && !issortedₑ(arguments(x))

# are there nested ⋆ terms?
function isnotflat(⋆)
    function (x)
        args = arguments(x)
        for t in args
            if iscall(t) && operation(t) === (⋆)
                return true
            end
        end
        return false
    end
end

function hasrepeats(x)
    length(x) <= 1 && return false
    for i=1:length(x)-1
        if isequal(x[i], x[i+1])
            return true
        end
    end
    return false
end

function merge_repeats(merge, xs)
    length(xs) <= 1 && return false
    merged = Any[]
    i=1

    while i<=length(xs)
        l = 1
        for j=i+1:length(xs)
            if isequal(xs[i], xs[j])
                l += 1
            else
                break
            end
        end
        if l > 1
            push!(merged, merge(xs[i], l))
        else
            push!(merged, xs[i])
        end
        i+=l
    end
    return merged
end

"""
    flatten_term(⋆, x)

Return a flattened expression with the numbers at the back.

# Example
```jldoctest
julia> @syms x y;

julia> SymbolicUtils.flatten_term(+, y + y + x)
x + 2y
```
"""
function flatten_term(⋆, x)
    args = arguments(x)
    # flatten nested ⋆
    flattened_args = []
    for t in args
        if iscall(t) && operation(t) === (⋆)
            append!(flattened_args, arguments(t))
        else
            push!(flattened_args, t)
        end
    end
    maketerm(typeof(x), ⋆, flattened_args, metadata(x))
end

function sort_args(f, t)
    args = arguments(t)
    if length(args) < 2
        return maketerm(typeof(t), f, args, metadata(t))
    elseif length(args) == 2
        x, y = args
        return maketerm(typeof(t), f, x <ₑ y ? [x,y] : [y,x], metadata(t))
    end
    args = args isa Tuple ? [args...] : args
    maketerm(typeof(t), f, sort(args, lt=<ₑ), metadata(t))
end

# Linked List interface
@inline assoc(d::ImmutableDict, k, v) = ImmutableDict(d, k=>v)

struct LL{V}
    v::V
    i::Int
end

islist(x) = iscall(x) || !isempty(x)

Base.empty(l::LL) = empty(l.v)
Base.isempty(l::LL) = l.i > length(l.v)

Base.length(l::LL) = length(l.v)-l.i+1
@inline car(l::LL) = l.v[l.i]
@inline cdr(l::LL) = isempty(l) ? empty(l) : LL(l.v, l.i+1)

function Base.length(t::BasicSymbolic)
    @match t.impl begin
        Term(_...) => length(arguments(t)) + 1 # PIRACY
        _ => 1
    end
end
Base.isempty(t::BasicSymbolic) = false
@inline car(t::BasicSymbolic) = operation(t)
@inline cdr(t::BasicSymbolic) = arguments(t)

@inline car(v) = iscall(v) ? operation(v) : first(v)
@inline function cdr(v)
    if iscall(v)
        arguments(v)
    else
        islist(v) ? LL(v, 2) : error("asked cdr of empty")
    end
end

@inline take_n(ll::LL, n) = isempty(ll) || n == 0 ? empty(ll) : @views ll.v[ll.i:n+ll.i-1] # @views handles Tuple
@inline take_n(ll, n) = @views ll[1:n]

@inline function drop_n(ll, n)
    if n === 0
        return ll
    else
        iscall(ll) ? drop_n(arguments(ll), n-1) : drop_n(cdr(ll), n-1)
    end
end
@inline drop_n(ll::Union{Tuple, AbstractArray}, n) = drop_n(LL(ll, 1), n)
@inline drop_n(ll::LL, n) = LL(ll.v, ll.i+n)

# Take a struct definition and make it be able to match in `@rule`
macro matchable(expr)
    @assert expr.head == :struct
    name = expr.args[2]
    if name isa Expr && name.head === :curly
        name = name.args[1]
    end
    fields = filter(x-> !(x isa LineNumberNode), expr.args[3].args)
    get_name(s::Symbol) = s
    get_name(e::Expr) = (@assert(e.head == :(::)); e.args[1])
    fields = map(get_name, fields)
    quote
        # TODO: fix this to be not a call. Make pattern matcher work for these
        $expr
        SymbolicUtils.head(::$name) = $name
        SymbolicUtils.operation(::$name) = $name
        SymbolicUtils.arguments(x::$name) = getfield.((x,), ($(QuoteNode.(fields)...),))
        SymbolicUtils.children(x::$name) = [SymbolicUtils.operation(x); SymbolicUtils.children(x)]
        Base.length(x::$name) = $(length(fields) + 1)
        SymbolicUtils.maketerm(x::$name, f, args, metadata) = f(args...)
    end |> esc
end

"""
  node_count(t)
Count the nodes in a symbolic expression tree satisfying `iscall` and `arguments`.
"""
node_count(t) = iscall(t) ? reduce(+, node_count(x) for x in arguments(t), init = 0) + 1 : 1

