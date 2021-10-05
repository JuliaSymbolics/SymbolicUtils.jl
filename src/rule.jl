
@inline alwaystrue(x) = true

# Matcher patterns with Slot and Segment

# matches one term
# syntax:  ~x
struct Slot{P}
    name::Symbol
    predicate::P
end

Slot(s) = Slot(s, alwaystrue)

Base.isequal(s1::Slot, s2::Slot) = s1.name == s2.name

Base.show(io::IO, s::Slot) = (print(io, "~"); print(io, s.name))

# matches zero or more terms
# syntax: ~~x
struct Segment{F}
    name::Symbol
    predicate::F
end

ismatch(s::Segment, t) = s.predicate(t)

Segment(s) = Segment(s, alwaystrue)

Base.show(io::IO, s::Segment) = (print(io, "~~"); print(io, s.name))

makesegment(s::Symbol, keys) = (push!(keys, s); Segment(s))

function makesegment(s::Expr, keys)
    if !(s.head == :(::))
        error("Syntax for specifying a segment is ~~x::\$predicate, where predicate is a boolean function")
    end

    name = s.args[1]

    push!(keys, name)
    :(Segment($(QuoteNode(name)), $(esc(s.args[2]))))
end

makeslot(s::Symbol, keys) = (push!(keys, s); Slot(s))

function makeslot(s::Expr, keys)
    if !(s.head == :(::))
        error("Syntax for specifying a slot is ~x::\$predicate, where predicate is a boolean function")
    end

    name = s.args[1]

    push!(keys, name)
    :(Slot($(QuoteNode(name)), $(esc(s.args[2]))))
end

function makepattern(expr, keys, slots, splat = false)
    res = if expr isa Expr
        if expr.head === :call
            if expr.args[1] === :(~)
                if expr.args[2] isa Expr && expr.args[2].head === :call expr.args[2].args[1] == :(~)
                    # matches ~~x::predicate or ~~x::predicate...
                    return makesegment(expr.args[2].args[2], keys)
                elseif splat
                    # matches ~x::predicate...
                    return makesegment(expr.args[2], keys)
                else
                    # matches ~x::predicate
                    return makeslot(expr.args[2], keys)
                end
            else
                :(term($(map(x->makepattern(x, keys, slots), expr.args)...); type=Any))
            end
        elseif expr.head === :...
            makepattern(expr.args[1], keys, slots, true)
        elseif expr.head == :(::) && expr.args[1] in slots
            return splat ? makesegment(expr, keys) : makeslot(expr, keys)
        elseif expr.head === :ref
            :(term(getindex, $(map(x->makepattern(x, keys, slots), expr.args)...); type=Any))
        elseif expr.head === :$
            esc(expr.args[1])
        else
            Expr(expr.head, makepattern.(expr.args, (keys,), (slots,))...)
        end
    elseif expr in slots
        return splat ? makesegment(expr, keys) : makeslot(expr, keys)
    else
        # treat as a literal
        esc(expr)
    end
    return splat ? Expr(:..., res) : res
end

function makeconsequent(expr)
    if expr isa Expr
        if expr.head === :call
            if expr.args[1] === :(~)
                if expr.args[2] isa Symbol
                    return :(getindex(__MATCHES__, $(QuoteNode(expr.args[2]))))
                elseif expr.args[2] isa Expr && expr.args[2].args[1] == :(~)
                    @assert expr.args[2].args[2] isa Symbol
                    return :(getindex(__MATCHES__, $(QuoteNode(expr.args[2].args[2]))))
                end
            else
                return Expr(:call, map(makeconsequent, expr.args)...)
            end
        else
            return Expr(expr.head, map(makeconsequent, expr.args)...)
        end
    else
        # treat as a literal
        return esc(expr)
    end
end

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
        maxdepth = reduce(max, (rule_depth(r, d+1, maxdepth) for r in arguments(rule)), init=1)
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
    rhs = r.rhs

    try
        # n == 1 means that exactly one term of the input (term,) was matched
        success(bindings, n) = n == 1 ? (@timer "RHS" rhs(bindings)) : nothing
        return r.matcher(success, (term,), EMPTY_DICT)
    catch err
        throw(RuleRewriteError(r, term))
    end
end

"""
    rewrite_rhs(expr::Expr)

Rewrite the `expr` by dealing with `:where` if necessary.
The `:where` is rewritten from, for example, `~x where f(~x)` to `f(~x) ? ~x : nothing`.
"""
function rewrite_rhs(expr::Expr)
    if expr.head == :where
        rhs = expr.args[1]
        predicate = expr.args[2]
        expr = :($predicate ? $rhs : nothing)
    end
    return expr
end
rewrite_rhs(expr) = expr

function addslots(expr, slots)
    if expr isa Expr
        if expr.head === :macrocall && expr.args[1] in [Symbol("@rule"), Symbol("@capture"), Symbol("@slots")]
            Expr(:macrocall, expr.args[1:2]..., slots..., expr.args[3:end]...)
        else
            Expr(expr.head, addslots.(expr.args, (slots,))...)
        end
    else
        expr
    end
end


"""
    @slots [SLOTS...] ex

Declare SLOTS as slot variables for all `@rule` or `@capture` invocations in the expression `ex`.

_Example:_

```julia
julia> @slots x y z a b c SymbolicUtils.Chain([
    (@rule x^2 + 2x*y + y^2 => (x + y)^2),
    (@rule x^a * y^b => (x*y)^a * y^(b-a)),
    (@rule +(x...) => sum(x)),
])
SymbolicUtils.Chain(SymbolicUtils.Rule{SymbolicUtils.Term{Any, Nothing}}[...]))
```

See also: [`@rule`](@ref), [`@capture`](@ref)
"""
macro slots(args...)
    length(args) >= 1 || ArgumentError("@slots requires at least one argument")
    slots = args[1:end-1]
    expr = args[end]

    return esc(addslots(expr, slots))
end

"""
    @rule [SLOTS...] LHS => RHS

Creates a `Rule` object. A rule object is callable, and takes an expression and
rewrites it if it matches the LHS pattern to the RHS expression, returns
`nothing` otherwise. The rule language is described below.

LHS can be any possibly nested function call expression where any of the arguments can
optionally be a Slot (`~x`) or a Segment (`~x...`) (described below).

SLOTS is an optional list of symbols to be interpted as slots or segments
directly (without using `~`).  To declare slots for several rules at once, see
the `@slots` macro.

If an expression matches LHS entirely, then it is rewritten to the result of the
expression RHS, whose local scope includes the slot matches as variables.

**Slot**:

A Slot variable is written as `~x` and matches a single expression. `x` is the name of the variable. If a slot appears more than once in an LHS expression then expression matched at every such location must be equal (as shown by `isequal`).

_Example:_

Simple rule to turn any `sin` into `cos`:

```julia
julia> @syms a b c
(a, b, c)

julia> r = @rule sin(~x) => cos(x)
sin(~x) => cos(x)

julia> r(sin(1+a))
cos((1 + a))
```

A rule with 2 segment variables

```julia
julia> r = @rule sin(~x + ~y) => sin(x)*cos(y) + cos(x)*sin(y)
sin(~x + ~y) => sin(x) * cos(y) + cos(x) * sin(y)

julia> r(sin(a + b))
cos(a)*sin(b) + sin(a)*cos(b)
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

A rule without `~`

```julia
julia> r = @slots x y z @rule x(y + z) => xy + xz
x(y + z) => xy + xz
```

**Segment**:

A Segment variable matches zero or more expressions in the function call.
Segments may be written by splatting slot variables (`~x...`).

_Example:_

This implements the distributive property of multiplication: `+(~ys...)` matches expressions
like `a + b`, `a+b+c` and so on. On the RHS `ys` presents as any old julia array.

```julia
julia> r = @rule ~x * +((~ys...)) => sum(map(y-> x * y, ys));

julia> r(2 * (a+b+c))
((2 * a) + (2 * b) + (2 * c))
```

A segment without `~`.

```julia
julia> r = @slots xs @rule min(xs...) => foldl(min, xs, Inf);

julia> r(min(a, b, c))
min(min(a, b), c)

**Predicates**:

There are two kinds of predicates, namely over slot variables and over the whole rule.
For the former, predicates can be used on both `~x` and `~x...` like `~x::f` or `~x::f...`.
Here `f` can be any julia function. In the case of a slot the function gets a single
matched subexpression, in the case of segment, it gets an array of matched expressions.

The predicate should return `true` if the current match is acceptable, and `false`
otherwise.

```julia
julia> two_πs(x::Number) = abs(round(x/(2π)) - x/(2π)) < 10^-9
two_πs (generic function with 1 method)

julia> two_πs(x) = false
two_πs (generic function with 2 methods)

julia> r = @slots x y z @rule sin(+(x..., y::two_πs, z...)) => sin(+(x..., z...))
sin(+(x..., y::two_πs, z...)) => sin(+(x..., z...))

julia> r(sin(a+3π))

julia> r(sin(a+6π))
sin(a)

julia> r(sin(a+6π+c))
sin((a + c))
```

For the predicate over the whole rule, use `@rule <LHS> => <RHS> where <predicate>`:

```
julia> @syms a b;

julia> predicate(x) = x === a;

julia> r = @rule ~x => x where f(x);

julia> r(a)
a

julia> r(b) === nothing
true
```

Note that this is syntactic sugar and that it is the same as something like
`@rule ~x => f(x) ? x : nothing`.

**Context**:

_In predicates_: Contextual predicates are functions wrapped in the `Contextual` type.
The function is called with 2 arguments: the expression and a context object
passed during a call to the Rule object (maybe done by passing a context to `simplify` or
a `RuleSet` object).

The function can use the inputs however it wants, and must return a boolean indicating
whether the predicate holds or not.

_In the consequent pattern_: Use `(@ctx)` to access the context object on the right hand side
of an expression.

**Compatibility**:
Segment variables may still be written as (`~~x`), and slot (`~x`) and segment (`~x...` or `~~x`) syntaxes on the RHS will still substitute the result of the matches.

See also: [`@capture`](@ref), [`@slots`](@ref)
"""
macro rule(args...)
    length(args) >= 1 || ArgumentError("@rule requires at least one argument")
    slots = args[1:end-1]
    expr = args[end]

    @assert expr.head == :call && expr.args[1] == :(=>)
    lhs = expr.args[2]
    rhs = rewrite_rhs(expr.args[3])
    keys = Symbol[]
    lhs_term = makepattern(lhs, keys, slots)
    unique!(keys)
    bind = Expr(:block, map(key-> :($(esc(key)) = getindex(__MATCHES__, $(QuoteNode(key)))), keys)...)
    quote
        $(__source__)
        lhs_pattern = $(lhs_term)
        Rule($(QuoteNode(expr)),
             lhs_pattern,
             matcher(lhs_pattern),
             __MATCHES__ -> ($bind; $(makeconsequent(rhs))),
             rule_depth($lhs_term))
    end
end

"""
    @capture [SLOTS...] ex pattern

Uses a `Rule` object to capture an expression if it matches the `pattern`. Returns `true` and injects
slot variable match results into the calling scope when the `pattern` matches, otherwise returns false. The
rule language for specifying the `pattern` is the same in @capture as it is in `@rule`. Contextual matching
is not yet supported.

```julia
julia> @syms a; ex = a^a;

julia> if @capture ex (~x)^(~x)
           @show x
       elseif @capture ex 2(~y)
           @show y
       end;
x = a
```

See also: [`@rule`](@ref), [`@slots`](@ref)
"""
macro capture(args...)
    length(args) >= 2 || ArgumentError("@capture requires at least two arguments")
    slots = args[1:end-2]
    ex = args[end-1]
    lhs = args[end]

    keys = Symbol[]
    lhs_term = makepattern(lhs, keys, slots)
    unique!(keys)
    bind = Expr(:block, map(key-> :($(esc(key)) = getindex(__MATCHES__, $(QuoteNode(key)))), keys)...)
    quote
        $(__source__)
        lhs_pattern = $(lhs_term)
        __MATCHES__ = Rule($(QuoteNode(lhs)),
             lhs_pattern,
             matcher(lhs_pattern),
             identity,
             rule_depth($lhs_term))($(esc(ex)))
        if __MATCHES__ !== nothing
            $bind
            true
        else
            false
        end
    end
end

#-----------------------------
#### Associative Commutative Rules

struct ACRule{F,R} <: AbstractRule
    sets::F
    rule::R
    arity::Int
end

Rule(acr::ACRule)   = acr.rule
getdepth(r::ACRule) = getdepth(r.rule)

macro acrule(expr)
    arity = length(expr.args[2].args[2:end])
    quote
        ACRule(permutations, $(esc(:(@rule($(expr))))), $arity)
    end
end

macro ordered_acrule(expr)
    arity = length(expr.args[2].args[2:end])
    quote
        ACRule(combinations, $(esc(:(@rule($(expr))))), $arity)
    end
end

Base.show(io::IO, acr::ACRule) = print(io, "ACRule(", acr.rule, ")")

function (acr::ACRule)(term)
    r = Rule(acr)
    if !istree(term)
        r(term)
    else
        f =  operation(term)
        # Assume that the matcher was formed by closing over a term
        if f != operation(r.lhs) # Maybe offer a fallback if m.term errors. 
            return nothing
        end

        T = symtype(term)
        args = unsorted_arguments(term)

        itr = acr.sets(eachindex(args), acr.arity)

        for inds in itr
            result = r(Term{T}(f, @views args[inds]))
            if result !== nothing
                # Assumption: inds are unique
                length(args) == length(inds) && return result
                return similarterm(term, f, [result, (args[i] for i in eachindex(args) if i ∉ inds)...], symtype(term))
            end
        end
    end
end


struct RuleRewriteError
    rule
    expr
end

getdepth(::Any) = typemax(Int)

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

Base.@deprecate RuleSet(x) Postwalk(Chain(x))
