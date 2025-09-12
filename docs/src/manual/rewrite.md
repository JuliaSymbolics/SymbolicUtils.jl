# Term Rewriting

## Rule-based rewriting

Rewrite rules match and transform an expression. A rule is written using either the `@rule` macro or the `@acrule` macro. It creates a callable `Rule` object.

### Basics of rule-based term rewriting in SymbolicUtils

Here is a simple rewrite rule, that uses formula for the double angle of the sine function:

```@example rewrite
using SymbolicUtils

@syms w z α::Real β::Real

(w, z, α, β) # hide

r1 = @rule sin(2(~x)) => 2sin(~x)*cos(~x)

r1(sin(2z))
```

The `@rule` macro takes a pair of patterns -- the _matcher_ and the _consequent_ (`@rule matcher => consequent`). If an expression matches the matcher pattern, it is rewritten to the consequent pattern. `@rule` returns a callable object that applies the rule to an expression.

`~x` in the example is what is a **slot variable** named `x`. In a matcher pattern, slot variables are placeholders that match exactly one expression. When used on the consequent side, they stand in for the matched expression. If a slot variable appears twice in a matcher pattern, all corresponding matches must be equal (as tested by `Base.isequal` function).

If you try to apply this rule to an expression with triple angle, it will return `nothing` -- this is the way a rule signifies failure to match.
```julia
r1(sin(3z))
```

Slot variable (matcher) is not necessary a single variable:
```@example rewrite
r1(sin(2*(w-z)))
```

And can also match a function:
```julia
r = @rule (~f)(z+1) => ~f

r(sin(z+1))
```
Rules are of course not limited to single slot variable

```@example rewrite
r2 = @rule sin(~x + ~y) => sin(~x)*cos(~y) + cos(~x)*sin(~y);

r2(sin(α+β))
```

Now let's say you want to catch the coefficients of a second degree polynomial in z. You can do that with:
```@example rewrite
c2d = @rule ~a + ~b*z + ~c*z^2 => (~a, ~b, ~c)

2d(3 + 2z + 5z^2)
```
Great! But if you try:
```julia
c2d(3 + 2z + z^2)

#output
nothing
```
the rule is not applied. This is because in the input polynomial there isn't a multiplication in front of the `z^2`. For this you can use **defslot variables**, with syntax `~!a`:
```@example rewrite
c2d = @rule ~!a + ~!b*z + ~!c*z^2 => (~a, ~b, ~c)

2d(3 + 2z + z^2)
```
They work like normal slot variables, but if they are not present they take a default value depending on the operation they are in, in the above example `~b = 1`. Currently defslot variables can be defined in:

Operation | Default value
----------|--------------
multiplication `*` | 1
addition `+` | 0
2nd argument of `^` | 1

If you want to match a variable number of subexpressions at once, you will need a **segment variable**. `~~xs` in the following example is a segment variable:

```@example rewrite
@syms x y z
@rule(+(~~xs) => ~~xs)(x + y + z)
```

`~~xs` is a vector of subexpressions matched. You can use it to construct something more useful:

```@example rewrite
r3 = @rule ~x * +(~~ys) => sum(map(y-> ~x * y, ~~ys));

r3(2 * (w+w+α+β))
```

Notice that the expression was autosimplified before application of the rule.

```@example rewrite
2 * (w+w+α+β)
```

Note that writing a single tilde `~` as consequent, will make the rule return a dictionary of [slot variable, expression matched].

```@example rewrite
r = @rule (~x + (~y)^(~m)) => ~

r(z+w^α)
```

### Predicates for matching

Matcher pattern may contain slot variables with attached predicates, written as `~x::f` where `f` is a function that takes a matched expression and returns a boolean value. Such a slot will be considered a match only if `f` returns true.

Similarly `~~x::g` is a way of attaching a predicate `g` to a segment variable. In the case of segment variables `g` gets a vector of 0 or more expressions and must return a boolean value. If the same slot or segment variable appears twice in the matcher pattern, then at most one of the occurrence should have a predicate.

For example,

```@example pred
using SymbolicUtils
@syms a b c d

r = @rule ~x + ~~y::(ys->iseven(length(ys))) => "odd terms";

@show r(a + b + c + d)
@show r(b + c + d)
@show r(b + c + b)
@show r(a + b)
```


### Associative-Commutative Rules

Given an expression `f(x, f(y, z, u), v, w)`, a `f` is said to be associative if the expression is equivalent to `f(x, y, z, u, v, w)` and commutative if the order of arguments does not matter.  SymbolicUtils has a special `@acrule` macro meant for rules on functions which are associate and commutative such as addition and multiplication of real and complex numbers.

```@example acr
using SymbolicUtils
@syms x y z

acr = @acrule((~a)^(~x) * (~a)^(~y) => (~a)^(~x + ~y))

acr(x^y * x^z)
```

although in case of `Number` it also works the same way with regular `@rule` since autosimplification orders and applies associativity and commutativity to the expression.

### Example of applying the rules to simplify expression

Consider expression `(cos(x) + sin(x))^2` that we would like simplify by applying some trigonometric rules. First, we need rule to expand square of `cos(x) + sin(x)`. First we try the simplest rule to expand square of the sum and try it on simple expression
```@example rewriteex
using SymbolicUtils

@syms x::Real y::Real

sqexpand = @rule (~x + ~y)^2 => (~x)^2 + (~y)^2 + 2 * ~x * ~y

sqexpand((cos(x) + sin(x))^2)
```

It works. This can be further simplified using Pythagorean identity and check it

```@example rewriteex
pyid = @rule sin(~x)^2 + cos(~x)^2 => 1

pyid(sin(x)^2 + 2sin(x)*cos(x) + cos(x)^2)===nothing
```

Why does it return `nothing`? If we look at the expression, we see that we have an additional addend `+ 2sin(x)*cos(x)`. Therefore, in order to work, the rule needs to be associative-commutative.

```@example rewriteex
acpyid = @acrule sin(~x)^2 + cos(~x)^2 => 1

acpyid(cos(x)^2 + sin(x)^2 + 2cos(x)*sin(x))
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

```@example composing
using SymbolicUtils
using SymbolicUtils.Rewriters

@syms x

sqexpand = @rule (~x + ~y)^2 => (~x)^2 + (~y)^2 + 2 * ~x * ~y
acpyid = @acrule sin(~x)^2 + cos(~x)^2 => 1

csa = Chain([sqexpand, acpyid])

csa((cos(x) + sin(x))^2)
```

Important feature of `Chain` is that it returns the expression instead of `nothing` if it doesn't change the expression

```@example composing
Chain([@acrule sin(~x)^2 + cos(~x)^2 => 1])((cos(x) + sin(x))^2)
```

it's important to notice, that chain is ordered, so if rules are in different order it wouldn't work the same as in earlier example

```@example composing
cas = Chain([acpyid, sqexpand])

cas((cos(x) + sin(x))^2)
```
since Pythagorean identity is applied before square expansion, so it is unable to match squares of sine and cosine.

One way to circumvent the problem of order of applying rules in chain is to use `RestartedChain`

```@example composing
using SymbolicUtils.Rewriters: RestartedChain

rcas = RestartedChain([acpyid, sqexpand])

rcas((cos(x) + sin(x))^2)
```

It restarts the chain after each successful application of a rule, so after `sqexpand` is hit it (re)starts again and successfully applies `acpyid` to resulting expression.

You can also use `Fixpoint` to apply the rules until there are no changes.

```@example composing
Fixpoint(cas)((cos(x) + sin(x))^2)
```
