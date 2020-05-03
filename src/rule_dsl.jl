
abstract type AbstractRule end # Currently doesn't really do anything. Can be removed.

#-----------------------------
#### Regular Rewriting Rules

struct Rule{L, M, R} <: AbstractRule
    expr::Expr               # rule pattern stored for pretty printing
    lhs::L                   # the pattern
    matcher::M               # matcher(lhs)
    rhs::R                   # consequent
    depth::Int               # number of levels of expr this rule touches
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

const EMPTY_DICT = ImmutableDict{Symbol, Any}(:____, nothing)

function (r::Rule)(term)
    match_function = r.matcher
    rhs = r.rhs

    match_function((term,),
                   EMPTY_DICT,
                   (d, n) -> n === 1 ? (@timer "RHS" rhs(d)) : nothing)
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
julia> @syms a b c
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
    quote
        lhs_pattern = $(lhs_term)
        Rule($(QuoteNode(expr)),
             lhs_pattern,
             matcher(lhs_pattern),
             __MATCHES__ -> $(makeconsequent(rhs)),
             rule_depth($lhs_term))
    end
end

macro acrule(expr)
    @assert expr.head == :call && expr.args[1] == :(=>)
    lhs,rhs = expr.args[2], expr.args[3]
    keys = Symbol[]
    lhs_op = lhs.args[1]
    lhs_term = :(ACMatcher($(makepattern(lhs, keys))))
    quote
        lhs_pattern = $(lhs_term)
        Rule($(QuoteNode(expr)),
             lhs_pattern,
             matcher(lhs_pattern),
             __MATCHES__ -> $(esc(lhs_op))($(makeconsequent(rhs)),
                                           Term{Number}($(esc(lhs_op)),
                                                        __MATCHES__[:__REST__])),
             rule_depth($lhs_term))
    end
end


#-----------------------------
#### Rulesets

"""
    RuleSet(rules::Vector{AbstractRules})(expr; depth=typemax(Int), applyall=false, recurse=true)

`RuleSet` is an `AbstractRule` which applies the given `rules` throughout an `expr`. 

`RuleSet(rules)(expr)` Note that this only applies the rules in one pass, not until there are no
changes to be applied. Use `SymbolicUtils.fixpoint(ruleset, expr)` to apply a RuleSet until there 
are no changes.

Keyword arguments:
* `recurse=true` Set whether or not the rules in the `RuleSet` are applied recursively to
subexpressions

* `depth=typemax(Int)` Set this argument to a positive integer to only recurse `depth` levels deep
into the expression. 

* `applyall=false` By default, `(::RuleSet)(ex)` will only apply rules to `ex` until one rule
matches at each `depth` level. Set `applyall` to `true` to ensure each rule gets applied.
"""
struct RuleSet <: AbstractRule
    rules::Vector{AbstractRule}
end


struct RuleRewriteError
    rule
    expr
end

function (r::RuleSet)(term; depth=typemax(Int), applyall=false, recurse=true)
    rules = r.rules
    term = to_symbolic(term)
    # simplify the subexpressions
    if depth == 0
        return term
    end
    if term isa Symbolic
        if term isa Term && recurse
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
                expr = r(expr′, depth=getdepth(rules[i]))# levels touched
                applyall || return expr
            end
        end
    else
        expr = term
    end
    return expr # no rule applied
end

getdepth(::RuleSet) = typemax(Int)

function fixpoint(f, x; kwargs...)
    x1 = f(x; kwargs...)
    while !isequal(x1, x)
        x = x1
        x1 = f(x; kwargs...)
    end
    return x1
end

fixpoint(f; kwargs...) = x -> fixpoint(f, x; kwargs...)

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


"""
    @timerewrite expr

If `expr` calls `simplify` or a `RuleSet` object, track the amount of time
it spent on applying each rule and pretty print the timing.

This uses [TimerOutputs.jl](https://github.com/KristofferC/TimerOutputs.jl).

## Example:

```julia

julia> expr = foldr(*, rand([a,b,c,d], 100))
(a ^ 26) * (b ^ 30) * (c ^ 16) * (d ^ 28)

julia> @timerewrite simplify(expr)
 ────────────────────────────────────────────────────────────────────────────────────────────────
                                                         Time                   Allocations
                                                 ──────────────────────   ───────────────────────
                Tot / % measured:                     340ms / 15.3%           92.2MiB / 10.8%

 Section                                 ncalls     time   %tot     avg     alloc   %tot      avg
 ────────────────────────────────────────────────────────────────────────────────────────────────
 ACRule((~y) ^ ~n * ~y => (~y) ^ (~n ...    667   11.1ms  21.3%  16.7μs   2.66MiB  26.8%  4.08KiB
   RHS                                       92    277μs  0.53%  3.01μs   14.4KiB  0.14%     160B
 ACRule((~x) ^ ~n * (~x) ^ ~m => (~x)...    575   7.63ms  14.6%  13.3μs   1.83MiB  18.4%  3.26KiB
 (*)(~(~(x::!issortedₑ))) => sort_arg...    831   6.31ms  12.1%  7.59μs    738KiB  7.26%     910B
   RHS                                      164   3.03ms  5.81%  18.5μs    250KiB  2.46%  1.52KiB
   ...
   ...
 ────────────────────────────────────────────────────────────────────────────────────────────────
(a ^ 26) * (b ^ 30) * (c ^ 16) * (d ^ 28)
```
"""
macro timerewrite(expr)
    :(timerewrite(()->$(esc(expr))))
end
