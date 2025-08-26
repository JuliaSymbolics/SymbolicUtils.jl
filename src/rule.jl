
@inline alwaystrue(x) = true
const COMM_CHECKS_LIMIT = Ref(10)

# Matcher patterns with Slot, DefSlot and Segment

# matches one term
# syntax:  ~x
struct Slot{P}
    name::Symbol
    predicate::P
end

Slot(s) = Slot(s, alwaystrue)

Base.isequal(s1::Slot, s2::Slot) = s1.name == s2.name

Base.show(io::IO, s::Slot) = (print(io, "~"); print(io, s.name))

# for when the slot is a symbol, like `~x`
makeslot(s::Symbol, keys) = (push!(keys, s); Slot(s))

# for when the slot is an expression, like `~x::predicate`
function makeslot(s::Expr, keys)
    if !(s.head == :(::))
        error("Syntax for specifying a slot is ~x::predicate, where predicate is a boolean function")
    end

    name = s.args[1]

    push!(keys, name)
    :(Slot($(QuoteNode(name)), $(esc(s.args[2]))))
end






# matches one term with built in default value.
# syntax: ~!x
# Example usage:
# (~!x + ~y) can match (a + b) but also just "a" and x takes default value of zero.
# (~!x)*(~y) can match a*b but also just "a", and x takes default value of one.
# (~x + ~y)^(~!z) can match (a + b)^c but also just "a + b", and z takes default value of one.
# only these three operations are supported for default values.

struct DefSlot{P, O}
    name::Symbol
    predicate::P
    operation::O
    defaultValue::Real
end

# operation | default
# + | 0
# * | 1
# ^ | 1
function defaultValOfCall(call)
    if call == :+
        return 0
    elseif call == :*
        return 1
    elseif call == :^
        return 1
    end
    # else no default value for this call
    error("You can use default slots only with +, * and ^, but you tried with: $call")
end

DefSlot(s) = DefSlot(s, alwaystrue, nothing, 0)
Base.isequal(s1::DefSlot, s2::DefSlot) = s1.name == s2.name
Base.show(io::IO, s::DefSlot) = (print(io, "~!"); print(io, s.name))

makeDefSlot(s::Symbol, keys, op) = (push!(keys, s); DefSlot(s, alwaystrue, op, defaultValOfCall(op)))

function makeDefSlot(s::Expr, keys, op)
    if !(s.head == :(::))
        error("Syntax for specifying a default slot is ~!x::\$predicate, where predicate is a boolean function")
    end

    name = s.args[1]

    push!(keys, name)
    tmp = defaultValOfCall(op)
    :(DefSlot($(QuoteNode(name)), $(esc(s.args[2])), $(esc(op)), $(esc(tmp))))
end





# matches zero or more terms
# syntax: ~~x
struct Segment{F}
    name::Symbol
    predicate::F
end

ismatch(s::Segment, t) = s.predicate(unwrap_const(t))

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

# parent call is needed to know which default value to give if any default slots are present
function makepattern(expr, keys, parentCall=nothing)
    if expr isa Expr
        if expr.head === :call
            if expr.args[1] === :(~)
                if expr.args[2] isa Expr && expr.args[2].args[1] == :(~)
                    # matches ~~x::predicate
                    makesegment(expr.args[2].args[2], keys)
                elseif expr.args[2] isa Expr && expr.args[2].args[1] == :(!)
                    # matches ~!x::predicate
                    makeDefSlot(expr.args[2].args[2], keys, parentCall)
                else
                    # matches ~x::predicate
                    makeslot(expr.args[2], keys)
                end
            elseif expr.args[1] === :(//)
                # bc when the expression is not quoted, 3//2 is a Rational{Int64}, not a call
                return esc(expr.args[2] // expr.args[3])
            else
                # make a pattern for every argument of the expr.
                :(term($(map(x->makepattern(x, keys, operation(expr)), expr.args)...); type=Any))
            end
        elseif expr.head === :ref
            :(term(getindex, $(map(x->makepattern(x, keys), expr.args)...); type=Any))
        elseif expr.head === :$
            return esc(expr.args[1])
        else
            Expr(expr.head, makepattern.(expr.args, (keys,))...)
        end
    else
        # treat as a literal
        return esc(expr)
    end
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
    elseif expr===:(~)
        return :(__MATCHES__)
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
    if iscall(rule)
        maxdepth = reduce(max, (rule_depth(r, d+1, maxdepth) for r in arguments(rule)), init=1)
    elseif rule isa Slot || rule isa Segment
        maxdepth = max(d, maxdepth)
    end
    return maxdepth
end

function Base.show(io::IO, r::Rule)
    Base.print(io, r.expr)
end

const EMPTY_IMMUTABLE_DICT = ImmutableDict{Symbol, Any}(:____, nothing)

function (r::Rule)(term)
    rhs = r.rhs

    try
        # n == 1 means that exactly one term of the input (term,) was matched
        success(bindings, n) = n == 1 ? (rhs(assoc(bindings, :MATCH, term))) : nothing
        return r.matcher(success, (term,), EMPTY_IMMUTABLE_DICT)
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

"""
    @rule LHS => RHS

Creates a `Rule` object. A rule object is callable, and  takes an expression and rewrites
it if it matches the LHS pattern to the RHS pattern, returns `nothing` otherwise.
The rule language is described below.

LHS can be any possibly nested function call expression where any of the arguments can
optionally be a Slot (`~x`), Default Value Slot (`~!x` also called DefSlot) or a Segment
 (`~~x`) (described below).

If an expression matches LHS entirely, then it is rewritten to the pattern in the RHS.
Slot, DefSlot and Segment variables on the RHS will substitute the result of the
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
julia> r = @rule sin(~x + ~y) => sin(~x)*cos(~y) + cos(~x)*sin(~y)
sin(~x + ~y) => sin(~x) * cos(~y) + cos(~x) * sin(~y)

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

**DefSlot**:

A DefSlot variable is written as `~!x`. Works like a normal slot, but can also take default values if not present in the expression.

_Example in power:_
```julia
julia> r_pow = @rule (~x)^(~!m) => ~m
(~x) ^ ~(!m) => ~m

julia> r_pow(x^2)
2

julia> r_pow(x)
1
```

_Example in sum:_
```julia
julia> r_sum = @rule ~x + ~!y => ~y
~x + ~(!y) => ~y

julia> r_sum(x+2)
x

julia> r_sum(x)
0
```

Currently DefSlot is implemented in:

Operation | Default value<br>
----------|--------------
\\* | 1
\\+ | 0
2nd argument of ^ | 1

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

There are two kinds of predicates, namely over slot variables and over the whole rule.
For the former, predicates can be used on both `~x` and `~~x` by using the `~x::f` or `~~x::f`.
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

For the predicate over the whole rule, use `@rule <LHS> => <RHS> where <predicate>`:

```
julia> @syms a b;

julia> predicate(x) = x === a;

julia> r = @rule ~x => ~x where predicate(~x);

julia> r(a)
a

julia> r(b) === nothing
true
```

Note that this is syntactic sugar and that it is the same as something like
`@rule ~x => f(~x) ? ~x : nothing`.

**Debugging Rules**:
Note that if the RHS is a single tilde `~`, then the rule returns a a dictionary of all [slot variable, expression matched], this is useful for debugging.

_Example:_

```julia
julia> r = @rule (~x + (~y)^(~m)) => ~
~x + (~y) ^ ~m => (~)

julia> r(a + b^2)
Base.ImmutableDict{Symbol, Any} with 5 entries:
  :MATCH => a + b^2
  :m     => 2
  :y     => b
  :x     => a
  :____  => nothing
```

**Context**:

_In predicates_: Contextual predicates are functions wrapped in the `Contextual` type.
The function is called with 2 arguments: the expression and a context object
passed during a call to the Rule object (maybe done by passing a context to `simplify` or
a `RuleSet` object).

The function can use the inputs however it wants, and must return a boolean indicating
whether the predicate holds or not.

_In the consequent pattern_: Use `(@ctx)` to access the context object on the right hand side
of an expression.
"""
macro rule(expr)
    @assert expr.head == :call && expr.args[1] == :(=>)
    lhs = expr.args[2]
    rhs = rewrite_rhs(expr.args[3])
    keys = Symbol[]
    lhs_term = makepattern(lhs, keys)
    unique!(keys)
    quote
        $(__source__)
        lhs_pattern = $(lhs_term)
        Rule(
            $(QuoteNode(expr)),
            lhs_pattern,
            matcher(lhs_pattern, permutations),
            __MATCHES__ -> $(makeconsequent(rhs)),
            rule_depth($lhs_term)
        )
    end
end

"""
    @capture ex pattern

Uses a `Rule` object to capture an expression if it matches the `pattern`. Returns `true` and injects
slot variable match results into the calling scope when the `pattern` matches, otherwise returns false. The
rule language for specifying the `pattern` is the same in @capture as it is in `@rule`. Contextual matching
is not yet supported

```julia
julia> @syms a; ex = a^a;

julia> if @capture ex (~x)^(~x)
           @show x
       elseif @capture ex 2(~y)
           @show y
       end;
x = a
```

See also: [`@rule`](@ref)
"""
macro capture(ex, lhs)
    keys = Symbol[]
    lhs_term = makepattern(lhs, keys)
    unique!(keys)
    bind = Expr(:block, map(key-> :($(esc(key)) = getindex(__MATCHES__, $(QuoteNode(key)))), keys)...)
    quote
        $(__source__)
        lhs_pattern = $(lhs_term)
        __MATCHES__ = Rule($(QuoteNode(lhs)),
             lhs_pattern,
             matcher(lhs_pattern, nothing),
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

"""
    @acrule(lhs => rhs)

Create an associative-commutative rule that matches all permutations of the arguments.

This macro creates a rule that can match patterns regardless of the order of arguments
in associative and commutative operations like addition and multiplication.

# Arguments
- `lhs`: The pattern to match (left-hand side)
- `rhs`: The replacement expression (right-hand side)

# Examples
```julia
julia> @syms x y z
(x, y, z)

julia> r = @acrule x + y => 2x  # Matches both x + y and y + x
ACRule(x + y => 2x)

julia> r(x + y)
2x

julia> r(y + x)
2x
```

See also: [`@rule`](@ref), [`@ordered_acrule`](@ref)
"""
macro acrule(expr)
    @assert expr.head == :call && expr.args[1] == :(=>)
    lhs = expr.args[2]
    rhs = rewrite_rhs(expr.args[3])
    keys = Symbol[]
    lhs_term = makepattern(lhs, keys)
    unique!(keys)

    arity = length(lhs.args[2:end])

    quote
        $(__source__)
        lhs_pattern = $(lhs_term)
        rule = Rule($(QuoteNode(expr)),
             lhs_pattern,
             matcher(lhs_pattern, permutations),
             __MATCHES__ -> $(makeconsequent(rhs)),
             rule_depth($lhs_term))
        ACRule(permutations, rule, $arity)
    end
end

macro ordered_acrule(expr)
    @assert expr.head == :call && expr.args[1] == :(=>)
    lhs = expr.args[2]
    rhs = rewrite_rhs(expr.args[3])
    keys = Symbol[]
    lhs_term = makepattern(lhs, keys)
    unique!(keys)

    arity = length(lhs.args[2:end])

    quote
        $(__source__)
        lhs_pattern = $(lhs_term)
        rule = Rule($(QuoteNode(expr)),
             lhs_pattern,
             matcher(lhs_pattern, combinations),
             __MATCHES__ -> $(makeconsequent(rhs)),
             rule_depth($lhs_term))
        ACRule(combinations, rule, $arity)
    end
end

Base.show(io::IO, acr::ACRule) = print(io, "ACRule(", acr.rule, ")")

function (acr::ACRule)(term)
    r = Rule(acr)
    if !iscall(term) || operation(term) != operation(r.lhs)
        # different operations -> try deflsot
        r(term)
    else
        f = operation(term)
        T = symtype(term)
        args = arguments(term)
        is_full_perm = acr.arity == length(args)
        if is_full_perm
            args_buf = copy(parent(args))
        else
            args_buf = ArgsT(@view args[1:acr.arity])
        end

        itr = acr.sets(eachindex(args), acr.arity)

        for inds in itr
            for (i, ind) in enumerate(inds)
                args_buf[i] = args[ind]
            end
            # this is temporary and only constructed so the rule can
            # try and match it - no need to hashcons it.
            tempterm = BSImpl.Term{T}(f, args_buf; unsafe = true)
            # this term will be hashconsed regardless
            result = r(tempterm)
            if result !== nothing
                # Assumption: inds are unique
                is_full_perm && return result
                inds_set = BitSet(inds)
                full_args_buf = ArgsT(@view args[1:(length(args)-acr.arity+1)])
                idx = 1
                for i in eachindex(args)
                    i in inds_set && continue
                    full_args_buf[idx] = args[i]
                    idx += 1
                end
                full_args_buf[idx] = maybe_const(result)
                return maketerm(typeof(term), f, full_args_buf, metadata(term))
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

Base.@deprecate RuleSet(x) Postwalk(Chain(x))
