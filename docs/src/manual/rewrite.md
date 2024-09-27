# Term Rewriting

## Rule-based rewriting

Rewrite rules match and transform an expression. A rule is written using either the `@rule` macro or the `@acrule` macro. It creates a callable `Rule` object.

### Basics of rule-based term rewriting in SymbolicUtils

Here is a simple rewrite rule, that uses formula for the double angle of the sine function:

```jldoctest rewrite
using SymbolicUtils

@syms w z α::Real β::Real

(w, z, α, β) # hide

r1 = @rule sin(2(~x)) => 2sin(~x)*cos(~x)

r1(sin(2z))

# output
2sin(z)*cos(z)
```

The `@rule` macro takes a pair of patterns -- the _matcher_ and the _consequent_ (`@rule matcher => consequent`). If an expression matches the matcher pattern, it is rewritten to the consequent pattern. `@rule` returns a callable object that applies the rule to an expression.

`~x` in the example is what is a **slot variable** named `x`. In a matcher pattern, slot variables are placeholders that match exactly one expression. When used on the consequent side, they stand in for the matched expression. If a slot variable appears twice in a matcher pattern, all corresponding matches must be equal (as tested by `Base.isequal` function). Hence this rule says: if you see something added to itself, make it twice of that thing, and works as such.

If you try to apply this rule to an expression with triple angle, it will return `nothing` -- this is the way a rule signifies failure to match.
```jldoctest rewrite
r1(sin(3z)) === nothing

# output
true
```

Slot variable (matcher) is not necessary a single variable

```jldoctest rewrite
r1(sin(2*(w-z)))

# output
2cos(w - z)*sin(w - z)
```

but it must be a single expression

```jldoctest rewrite
r1(sin(2*(w+z)*(α+β))) === nothing

# output
true
```

Rules are of course not limited to single slot variable

```jldoctest rewrite
r2 = @rule sin(~x + ~y) => sin(~x)*cos(~y) + cos(~x)*sin(~y);

r2(sin(α+β))

# output
sin(β)*cos(α) + cos(β)*sin(α)
```

If you want to match a variable number of subexpressions at once, you will need a **segment variable**. `~~xs` in the following example is a segment variable:

```jldoctest rewrite
@syms x y z
@rule(+(~~xs) => ~~xs)(x + y + z)

# output
3-element view(::Vector{SymbolicUtils.BasicSymbolic}, 1:3) with eltype SymbolicUtils.BasicSymbolic:
 z
 y
 x
```

`~~xs` is a vector of subexpressions matched. You can use it to construct something more useful:

```jldoctest rewrite
r3 = @rule ~x * +(~~ys) => sum(map(y-> ~x * y, ~~ys));

r3(2 * (w+w+α+β))

# output
4w + 2α + 2β
```

Notice that the expression was autosimplified before application of the rule.

```jldoctest rewrite
2 * (w+w+α+β)

# output
2(2w + α + β)
```

### Predicates for matching

Matcher pattern may contain slot variables with attached predicates, written as `~x::f` where `f` is a function that takes a matched expression and returns a boolean value. Such a slot will be considered a match only if `f` returns true.

Similarly `~~x::g` is a way of attaching a predicate `g` to a segment variable. In the case of segment variables `g` gets a vector of 0 or more expressions and must return a boolean value. If the same slot or segment variable appears twice in the matcher pattern, then at most one of the occurrence should have a predicate.

For example,

```jldoctest pred
using SymbolicUtils
@syms a b c d

r = @rule ~x + ~~y::(ys->iseven(length(ys))) => "odd terms";

@show r(a + b + c + d)
@show r(b + c + d)
@show r(b + c + b)
@show r(a + b)

# output
r(a + b + c + d) = nothing
r(b + c + d) = "odd terms"
r(b + c + b) = nothing
r(a + b) = nothing
```


### Associative-Commutative Rules

Given an expression `f(x, f(y, z, u), v, w)`, a `f` is said to be associative if the expression is equivalent to `f(x, y, z, u, v, w)` and commutative if the order of arguments does not matter.  SymbolicUtils has a special `@acrule` macro meant for rules on functions which are associate and commutative such as addition and multiplication of real and complex numbers.

```jldoctest acr
using SymbolicUtils
@syms x y z

acr = @acrule((~a)^(~x) * (~a)^(~y) => (~a)^(~x + ~y))

acr(x^y * x^z)

# output
x^(y + z)
```

although in case of `Number` it also works the same way with regular `@rule` since autosimplification orders and applies associativity and commutativity to the expression.

### Example of applying the rules to simplify expression

Consider expression `(cos(x) + sin(x))^2` that we would like simplify by applying some trigonometric rules. First, we need rule to expand square of `cos(x) + sin(x)`. First we try the simplest rule to expand square of the sum and try it on simple expression
```jldoctest rewriteex
using SymbolicUtils

@syms x::Real y::Real

sqexpand = @rule (~x + ~y)^2 => (~x)^2 + (~y)^2 + 2 * ~x * ~y

sqexpand((cos(x) + sin(x))^2)

# output
sin(x)^2 + 2sin(x)*cos(x) + cos(x)^2
```

It works. This can be further simplified using Pythagorean identity and check it

```jldoctest rewriteex
pyid = @rule sin(~x)^2 + cos(~x)^2 => 1

pyid(cos(x)^2 + sin(x)^2) === nothing

# output
true
```

Why does it return `nothing`? If we look at the rule, we see that the order of `sin(x)` and `cos(x)` is different. Therefore, in order to work, the rule needs to be associative-commutative.

```jldoctest rewriteex
acpyid = @acrule sin(~x)^2 + cos(~x)^2 => 1

acpyid(cos(x)^2 + sin(x)^2 + 2cos(x)*sin(x))

# output
1 + 2sin(x)*cos(x)
```

It has been some work. Fortunately rules may be [chained together](#chaining rewriters) into more sophisticated rewriters to avoid manual application of the rules.


## Composing rewriters

A rewriter is any callable object which takes an expression and returns an expression
or `nothing`. If `nothing` is returned that means there was no changes applicable
to the input expression. The Rules we created above are rewriters.

The `SymbolicUtils.Rewriters` module contains some types which create and transform
rewriters.

- `Empty()` is a rewriter which always returns `nothing`
- `Chain(itr)` chain an iterator of rewriters into a single rewriter which applies
   each chained rewriter in the given order.
   If a rewriter returns `nothing` this is treated as a no-change.
- `RestartedChain(itr)` like `Chain(itr)` but restarts from the first rewriter once on the
   first successful application of one of the chained rewriters.
- `IfElse(cond, rw1, rw2)` runs the `cond` function on the input, applies `rw1` if cond
   returns true, `rw2` if it returns false
- `If(cond, rw)` is the same as `IfElse(cond, rw, Empty())`
- `Prewalk(rw; threaded=false, thread_cutoff=100)` returns a rewriter which does a pre-order 
   (*from top to bottom and from left to right*) traversal of a given expression and applies 
   the rewriter `rw`. `threaded=true` will use multi threading for traversal.
   Note that if `rw` returns `nothing` when a match is not found, then `Prewalk(rw)` will
   also return nothing unless a match is found at every level of the walk. If you are
   applying multiple rules, then `Chain` already has the appropriate passthrough behavior.
   If you only want to apply one rule, then consider using `PassThrough`.
   `thread_cutoff` 
   is the minimum number of nodes in a subtree which should be walked in a threaded spawn.
- `Postwalk(rw; threaded=false, thread_cutoff=100)` similarly does post-order 
   (*from left to right and from bottom to top*) traversal.
- `Fixpoint(rw)` returns a rewriter which applies `rw` repeatedly until there are no changes to be made.
- `PassThrough(rw)` returns a rewriter which if `rw(x)` returns `nothing` will instead
   return `x` otherwise will return `rw(x)`.

### Chaining rewriters

Several rules may be chained to give chain of rules. Chain is an array of rules which are subsequently applied to the expression.

To check that, we will combine rules from [previous example](#example of applying the rules to simplify expression) into a chain

```jldoctest composing
using SymbolicUtils
using SymbolicUtils.Rewriters

@syms x

sqexpand = @rule (~x + ~y)^2 => (~x)^2 + (~y)^2 + 2 * ~x * ~y
acpyid = @acrule sin(~x)^2 + cos(~x)^2 => 1

csa = Chain([sqexpand, acpyid])

csa((cos(x) + sin(x))^2)

# output
1 + 2sin(x)*cos(x)
```

Important feature of `Chain` is that it returns the expression instead of `nothing` if it doesn't change the expression

```jldoctest composing
Chain([@acrule sin(~x)^2 + cos(~x)^2 => 1])((cos(x) + sin(x))^2)

# output
(sin(x) + cos(x))^2
```

it's important to notice, that chain is ordered, so if rules are in different order it wouldn't work the same as in earlier example

```jldoctest composing
cas = Chain([acpyid, sqexpand])

cas((cos(x) + sin(x))^2)

# output
sin(x)^2 + 2sin(x)*cos(x) + cos(x)^2
```
since Pythagorean identity is applied before square expansion, so it is unable to match squares of sine and cosine.

One way to circumvent the problem of order of applying rules in chain is to use `RestartedChain`

```jldoctest composing
using SymbolicUtils.Rewriters: RestartedChain

rcas = RestartedChain([acpyid, sqexpand])

rcas((cos(x) + sin(x))^2)

# output
1 + 2sin(x)*cos(x)
```

It restarts the chain after each successful application of a rule, so after `sqexpand` is hit it (re)starts again and successfully applies `acpyid` to resulting expression.

You can also use `Fixpoint` to apply the rules until there are no changes.

```jldoctest composing
Fixpoint(cas)((cos(x) + sin(x))^2)

# output
1 + 2sin(x)*cos(x)
```
