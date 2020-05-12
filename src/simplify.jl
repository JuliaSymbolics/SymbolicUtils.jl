##### Numeric simplification

"""
    default_rules(expr, context::T)::RuleSet

The `RuleSet` to be used by default for a given expression and the context.
Julia packages defining their own context types should define this method.

By default SymbolicUtils will try to apply appropriate rules for expressions
of symtype Number.
"""
default_rules(x, ctx) = SIMPLIFY_RULES

"""
    simplify(x, ctx=EmptyCtx();
        rules=default_rules(x, ctx),
        fixpoint=true,
        applyall=true,
        recurse=true)

Simplify an expression by applying `rules` until there are no changes.
The second argument, the context is passed to every [`Contextual`](#Contextual)
predicate and can be accessed as `(@ctx)` in the right hand side of `@rule` expression.

By default the context is an `EmptyCtx()` -- which means there is no contextual information.
Any arbitrary type can be used as a context, and packages defining their own contexts
should define `default_rules(ctx::TheContextType)` to return a `RuleSet` that will
be used by default while simplifying under that context.

If `fixpoint=true` this will repeatedly apply the set of rules until there are no changes.
Applies them once if `fixpoint=false`.

The `applyall` and `recurse` keywords are forwarded to the enclosed
`RuleSet`, they are mainly used for internal optimization.
"""
function simplify(x, ctx=EmptyCtx(); rules=default_rules(x, ctx), fixpoint=true, applyall=true, kwargs...)
    if fixpoint
        SymbolicUtils.fixpoint(rules, x, ctx; applyall=applyall)
    else
        rules(x, ctx; applyall=applyall, kwargs...)
    end
end


Base.@deprecate simplify(x, rules::RuleSet; kwargs...)  simplify(x, rules=rules; kwargs...)

"""
    substitute(expr, dict)

substitute any subexpression that matches a key in `dict` with
the corresponding value.
"""
function substitute(expr, dict)
    RuleSet([@rule ~x::(x->haskey(dict, x)) => dict[~x]])(expr)
end

### Predicates

sym_isa(::Type{T}) where {T} = @nospecialize(x) -> x isa T || symtype(x) <: T
is_operation(f) = @nospecialize(x) -> (x isa Term) && (operation(x) == f)

isliteral(::Type{T}) where {T} = x -> x isa T
isnumber(x) = isliteral(Number)(x)

_iszero(t) = false
_iszero(x::Number) = iszero(x)
_isone(t) = false
_isone(x::Number) = isone(x)

issortedₑ(rev=false) = args -> issorted(args, lt=<ₑ, rev=rev)

# are there nested ⋆ terms?
function isnotflat(⋆)
    function (args)
        for t in args
            if t isa Term && operation(t) === (⋆)
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

### Simplification rules

pow(x,y) = y==0 ? 1 : y<0 ? inv(x)^(-y) : x^y
pow(x::Symbolic,y) = y==0 ? 1 : Base.:^(x,y)
pow(x, y::Symbolic) = Base.:^(x,y)
pow(x::Symbolic,y::Symbolic) = Base.:^(x,y)

# Numbers to the back
function flatten_term(⋆, args)
    # flatten nested ⋆
    flattened_args = []
    for t in args
        if t isa Term && operation(t) === (⋆)
            append!(flattened_args, arguments(t))
        else
            push!(flattened_args, t)
        end
    end
    Term(⋆, flattened_args)
end

function sort_args(f, args, rev=false)
    if length(args) < 2
        return Term(f, args)
    elseif length(args) == 2
        x, y = args
        return Term(f, x <ₑ y ? [x,y] : [y,x])
    end
    args = args isa Tuple ? [args...] : args
    Term(f, sort(args, lt=<ₑ, rev=rev))
end
