using Base: ImmutableDict

"""
    $TYPEDSIGNATURES

Check if a number is an integer and within safe bounds for `Int`.

# Arguments
- `x`: The value to check (either a `Number` or other type)

# Returns
- `true` if `x` is an integer with absolute value less than `typemax(Int)`, `false` otherwise

# Details
This function ensures that integer values are safe to convert to `Int` without overflow.
For non-numeric types, always returns `false`. The bounds check prevents issues with
very large integers that cannot be accurately represented as `Int`.
"""
safe_isinteger(@nospecialize(x::Number)) = isinteger(x) && abs(x) < typemax(Int)
safe_isinteger(x) = false

"""
    $TYPEDSIGNATURES

Safe power operation that handles special cases for symbolic and numeric values.

# Arguments
- `x`: The base (can be numeric or symbolic)
- `y`: The exponent (can be numeric or symbolic)

# Returns
- The result of `x^y` with special handling for edge cases

# Details
This function provides a safe implementation of exponentiation with special case handling:
- For numeric exponents: `y==0` returns `1`, `y<0` uses `inv(x)^(-y)` for numerical stability
- For symbolic values: delegates to `Base.:^` to maintain proper symbolic behavior
Multiple dispatch ensures correct behavior for all combinations of numeric and symbolic arguments.
"""
pow(x,y) = y==0 ? 1 : y<0 ? inv(x)^(-y) : x^y
pow(x::BasicSymbolic,y) = y==0 ? 1 : Base.:^(x,y)
pow(x, y::BasicSymbolic) = Base.:^(x,y)
pow(x::BasicSymbolic,y::BasicSymbolic) = Base.:^(x,y)

# Simplification utilities
"""
    $TYPEDSIGNATURES

Check if a term contains trigonometric or exponential functions.

# Arguments
- `term`: The symbolic term to check

# Returns
- `true` if the term contains any of: `sin`, `cos`, `tan`, `cot`, `sec`, `csc`, `exp`, `cosh`, `sinh`
- `false` otherwise

# Details
This function recursively searches a symbolic expression tree to determine if it contains
any trigonometric or exponential functions. It checks both the operation at the current
level and recursively checks all arguments. Used by simplification routines to identify
expressions requiring special handling.
"""
function has_trig_exp(term)
    !iscall(term) && return false
    fns = (sin, cos, tan, cot, sec, csc, exp, cosh, sinh)
    op = operation(term)

    if Base.@nany 9 i->fns[i] === op
        return true
    else
        return any(has_trig_exp, parent(arguments(term)))
    end
end

### Predicates

sym_isa(::Type{T}) where {T} = @nospecialize(x) -> x isa T || symtype(x) <: T

isliteral(::Type{T}) where {T} = x -> x isa T
is_literal_number(x) = isliteral(Number)(unwrap_const(x))

# checking the type directly is faster than dynamic dispatch in type unstable code
"""
    $TYPEDSIGNATURES

Check if a value is zero, with caching for performance.

# Arguments
- `x`: The value to check (can be a number, array, or symbolic expression)

# Returns
- `true` if the unwrapped value is zero, `false` otherwise

# Details
This cached function efficiently checks if a value is zero by first unwrapping any
constant wrappers. Handles both numeric values and arrays. Returns `false` for symbolic
expressions that are not constant zero. The `@cache` macro improves performance by
memoizing results for previously seen values.
"""
@cache function _iszero(x)::Bool
    @nospecialize x
    x = unwrap_const(unwrap(x))
    x isa Number && return iszero(x)::Bool
    x isa Array && return iszero(x)::Bool
    return false
end
"""
    $TYPEDSIGNATURES

Check if a value is one, with caching for performance.

# Arguments
- `x`: The value to check (can be a number, array, or symbolic expression)

# Returns
- `true` if the unwrapped value is one, `false` otherwise

# Details
This cached function efficiently checks if a value is one by first unwrapping any
constant wrappers. Handles both numeric values and arrays. Returns `false` for symbolic
expressions that are not constant one. The `@cache` macro improves performance by
memoizing results for previously seen values.
"""
@cache function _isone(x)::Bool
    @nospecialize x
    x = unwrap_const(unwrap(x))
    x isa Number && return isone(x)::Bool
    x isa Array && return isone(x)::Bool
    return false
end
"""
    $TYPEDSIGNATURES

Check if a value is an integer (numeric or symbolic with integer type).

# Arguments
- `x`: The value to check

# Returns
- `true` if `x` is a numeric integer or a symbolic with `Integer` symtype, `false` otherwise

# Details
This predicate returns `true` for both concrete integer values and symbolic expressions
with integer type annotations. Used in simplification and code generation to determine
when integer-specific optimizations can be applied.
"""
_isinteger(x) = (x isa Number && isinteger(x)) || (x isa BasicSymbolic && symtype(x) <: Integer)

"""
    $TYPEDSIGNATURES

Check if a value is real (numeric or symbolic with real type).

# Arguments
- `x`: The value to check

# Returns
- `true` if `x` is a numeric real or a symbolic with `Real` symtype, `false` otherwise

# Details
This predicate returns `true` for both concrete real values and symbolic expressions
with real type annotations. Used in simplification and rewriting to enable real-specific
mathematical transformations.
"""
_isreal(x) = (x isa Number && isreal(x)) || (x isa BasicSymbolic && symtype(x) <: Real)

issortedₑ(args) = issorted(args, lt=<ₑ)

"""
    $TYPEDSIGNATURES

Create a predicate that checks if an expression with operation `f` needs argument sorting.

# Arguments
- `f`: The operation to check for

# Returns
- A function that returns `true` if an expression has operation `f` and unsorted arguments

# Details
Returns a predicate function that checks whether a given expression:
1. Has operation `f`
2. Has arguments that are not sorted according to the `<ₑ` ordering

This is used in simplification to identify expressions that need canonicalization through
argument sorting.
"""
needs_sorting(f) = x -> is_operation(f)(x) && !issortedₑ(arguments(x))

# are there nested ⋆ terms?
"""
    $TYPEDSIGNATURES

Create a predicate that checks if an expression has nested operations of type `⋆`.

# Arguments
- `⋆`: The operation to check for nesting

# Returns
- A function that returns `true` if any argument has operation `⋆` (indicating nesting)

# Details
Returns a predicate function that checks whether an expression contains nested instances
of the same operation. For example, if `⋆` is `*`, this would detect `*(x, *(y, z))`
which should be flattened to `*(x, y, z)`. Used in normalization to identify expressions
that need flattening.
"""
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

"""
    $TYPEDSIGNATURES

Check if a sequence has consecutive repeated elements.

# Arguments
- `x`: A sequence (array or tuple) to check

# Returns
- `true` if any element is equal to the next element, `false` otherwise

# Details
This function scans through a sequence to detect consecutive duplicates. Returns `false`
for sequences of length 0 or 1. Uses `isequal` for comparison, which handles symbolic
expressions correctly. Used in simplification to identify terms that can be merged
(e.g., `x + x` → `2x`).
"""
function hasrepeats(x)
    length(x) <= 1 && return false
    for i=1:length(x)-1
        if isequal(x[i], x[i+1])
            return true
        end
    end
    return false
end

"""
    $TYPEDSIGNATURES

Merge consecutive repeated elements in a sequence using a combining function.

# Arguments
- `merge`: A function `(element, count) -> merged_value` to combine repeated elements
- `xs`: The sequence to process

# Returns
- A new sequence with consecutive repeats merged, or `false` if `xs` has length ≤ 1

# Details
This function scans through a sequence and merges consecutive equal elements by calling
`merge(element, count)` where `count` is the number of repetitions. For example, with
`merge = (x, n) -> n*x`, this transforms `[x, x, x, y]` to `[3x, y]`. Elements that
don't repeat are kept as-is. Uses `isequal` for comparison.
"""
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

"""
    $TYPEDSIGNATURES

Sort the arguments of a term according to the canonical ordering `<ₑ`.

# Arguments
- `f`: The operation of the term
- `t`: The term whose arguments should be sorted

# Returns
- A new term with the same operation and metadata, but with arguments sorted by `<ₑ`

# Details
This function creates a canonical form for commutative operations by sorting arguments.
For 0-1 arguments, returns unchanged. For 2 arguments, performs a direct comparison.
For more arguments, sorts using the full `<ₑ` ordering. This ensures expressions like
`x + y` and `y + x` have the same representation.
"""
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
@inline function assoc(d::ImmutableDict{Symbol, Any}, k::Symbol, v::Any)
    @nospecialize v
    ImmutableDict(d, k, unwrap_const(v))
end

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

Base.length(t::Term) = length(arguments(t)) + 1 # PIRACY
Base.isempty(t::Term) = false
@inline car(t::Term) = operation(t)
@inline cdr(t::Term) = arguments(t)

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
    if Meta.isexpr(name, :<:)
        name = name.args[1]
    end
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

