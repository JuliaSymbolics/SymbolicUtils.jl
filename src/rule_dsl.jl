
abstract type AbstractRule end # Currently doesn't really do anything. Can be removed.

#-----------------------------
#### Regular Rewriting Rules

struct Rule{L, M, R} <: AbstractRule
    expr::Expr               # rule pattern stored for pretty printing
    lhs::L                   # the pattern
    matcher::M               # matcher(lhs)
    rhs::R                   # consequent
    depth::Int               # number of levels of expr this rule touches
    _init_matches::MatchDict # empty dictionary with the required fields set to nothing, see MatchDict
end

getdepth(r::Rule) = r.depth

function rule_depth(rule, d=0, maxdepth=0)
    if rule isa Term
        maxdepth = maximum(rule_depth(r, d+1, maxdepth) for r in arguments(rule))
    elseif rule isa Slot || rule isa Segment
        maxdepth = max(d, maxdepth)
    end
    return maxdepth
end

function Base.show(io::IO, r::Rule)
    Base.print(io, r.expr)
end

function (r::Rule)(term)
    m, rhs, dict = r.matcher, r.rhs, r._init_matches
    m((term,), dict, (d, n) -> n == 1 ? (@timer "RHS" rhs(d)) : nothing)
end

"""
    `@rule LHS => RHS`

Creates a `Rule` object. A rule object is callable, and  takes an expression and rewrites
it if it matches the LHS pattern to the RHS pattern, returns `nothing` otherwise.
The rule language is described below.

LHS can be any possibly nested function call expression where any of the arugments can
optionally be a Slot (`~x`) or a Segment (`~~x`) (described below).

If an expression matches LHS entirely, then it is rewritten to the pattern in the RHS
Segment (`~x`) and slot variables (`~~x`) on the RHS will substitute the result of the
matches found for these variables in the LHS.

**Slot**:

A Slot variable is written as `~x` and matches a single expression. `x` is the name of the variable. If a slot appears more than once in an LHS expression then expression matched at every such location must be equal (as shown by `isequal`).

_Example:_

Simple rule to turn any `sin` into `cos`:

```julia
julia> @vars a b c
(a, b, c)

julia> r = @rule sin(~x) => cos(~x)
sin(~x) => cos(~x)

julia> r(sin(1+a))
cos((1 + a))
```

A rule with 2 segment variables

```julia
julia> r = @rule ~x - ~y => ~x + (-(~y))
~x - ~y => ~x + -(~y)

julia> r(a-2b)
(a + (-(2 * b)))
```

A rule that matches two of the same expressions:

```julia
julia> r = @rule sin(~x)^2 + cos(~x)^2 => 1
sin(~x) ^ 2 + cos(~x) ^ 2 => 1

julia> r(sin(2a)^2 + cos(2a)^2)
1

julia> r(sin(2a)^2 + cos(a)^2)
# nothing
```

**Segment**:

A Segment variable is written as `~~x` and matches zero or more expressions in the
function call.

_Example:_

This implements the distributive property of multiplication: `+(~~ys)` matches expressions
like `a + b`, `a+b+c` and so on. On the RHS `~~ys` presents as any old julia array.

```julia
julia> r = @rule ~x * +((~~ys)) => sum(map(y-> ~x * y, ~~ys));

julia> r(2 * (a+b+c))
((2 * a) + (2 * b) + (2 * c))
```

**Predicates**:

Predicates can be used on both `~x` and `~~x` by using the `~x::f` or `~~x::f`.
Here `f` can be any julia function. In the case of a slot the function gets a single
matched subexpression, in the case of segment, it gets an array of matched expressions.

The predicate should return `true` if the current match is acceptable, and `false`
otherwise.

```julia
julia> two_πs(x::Number) = abs(round(x/(2π)) - x/(2π)) < 10^-9
two_πs (generic function with 1 method)

julia> two_πs(x) = false
two_πs (generic function with 2 methods)

julia> r = @rule sin(~~x + ~y::two_πs + ~~z) => sin(+(~~x..., ~~z...))
sin(~(~x) + ~(y::two_πs) + ~(~z)) => sin(+(~(~x)..., ~(~z)...))

julia> r(sin(a+3π))

julia> r(sin(a+6π))
sin(a)

julia> r(sin(a+6π+c))
sin((a + c))
```

Predicate function gets an array of values if attached to a segment variable (`~~x`).
"""
macro rule(expr)
    @assert expr.head == :call && expr.args[1] == :(=>)
    lhs,rhs = expr.args[2], expr.args[3]
    keys = Symbol[]
    lhs_term = makepattern(lhs, keys)
    unique!(keys)
    dict = matchdict(keys)
    quote
        lhs_pattern = $(lhs_term)
        Rule($(QuoteNode(expr)),
             lhs_pattern,
             matcher(lhs_pattern),
             __MATCHES__ -> $(makeconsequent(rhs)),
             rule_depth($lhs_term),
             $dict)
    end
end

#-----------------------------
#### Associative Commutative Rules

struct ACRule{L, M, R} <: AbstractRule
    rule::Rule{L, M, R}
    arity::Int
end

Rule(acr::ACRule)   = acr.rule
getdepth(r::ACRule) = getdepth(r.rule)

macro acrule(expr)
    arity = length(expr.args[2].args[2:end])
    quote
        ACRule(@rule($expr), $arity)
    end
end

Base.show(io::IO, acr::ACRule) = print(io, "ACRule(", acr.rule, ")")

function (acr::ACRule)(term)
    r = Rule(acr)
    if term isa Variable
        r(term)
    else
        f =  operation(term)
        # Assume that the matcher was formed by closing over a term
        if f != operation(r.lhs) # Maybe offer a fallback if m.term errors. 
            return nothing
        end
        
        T = symtype(term)
        args = arguments(term)
        
        for inds in permutations(eachindex(args), acr.arity)
            result = r(Term{T}(f, args[inds]))
            if !isnothing(result)
                return Term{T}(f, [result, (args[i] for i in eachindex(args) if i ∉ inds)...])
            end
        end
    end
end

#-----------------------------
#### Rulesets

struct RuleSet <: AbstractRule
    rules::Vector{AbstractRule}
end

struct RuleRewriteError
    rule
    expr
end

function (r::RuleSet)(term; depth=typemax(Int))
    rules = r.rules
    # simplify the subexpressions
    if depth == 0
        return term
    end
    if term isa Symbolic
        if term isa Term
            expr = Term{symtype(term)}(operation(term),
                                       map(t -> r(t, depth=depth-1), arguments(term)))
        else
            expr = term
        end
        for i in 1:length(rules)
            expr′ = try
                @timer(repr(rules[i]), rules[i](expr))
            catch err
                throw(RuleRewriteError(rules[i], expr))
            end
            if expr′ === nothing
                # this rule doesn't apply
                continue
            else
                return r(expr′, depth=getdepth(rules[i])) # levels touched
            end
        end
    else
        expr = term
    end
    return expr # no rule applied
end

@noinline function Base.showerror(io::IO, err::RuleRewriteError)
    msg = "Failed to apply rule $(err.rule) on expression "
    msg *= sprint(io->showraw(io, err.expr))
    print(io, msg)
end

function timerewrite(f)
    if !TIMER_OUTPUTS
        error("timerewrite must be called after enabling " *
              "TIMER_OUTPUTS in the main file of this package")
    end
    reset_timer!()
    being_timed[] = true
    x = f()
    being_timed[] = false
    print_timer()
    println()
    x
end

macro timerewrite(expr)
    :(timerewrite(()->$(esc(expr))))
end
