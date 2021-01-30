# Term Rewriting

## Rule-based rewriting

Rewrite rules match and transform an expression. A rule is written using either the `@rule` macro or the `@acrule` macro.

Here is a simple rewrite rule:

```julia:rewrite1
r1 = @rule ~x + ~x => 2 * (~x)

r1(sin(1+z) + sin(1+z))
```

The `@rule` macro takes a pair of patterns -- the _matcher_ and the _consequent_ (`@rule matcher => consequent`). If an expression matches the matcher pattern, it is rewritten to the consequent pattern. `@rule` returns a callable object that applies the rule to an expression.

`~x` in the example is what is a **slot variable** named `x`. In a matcher pattern, slot variables are placeholders that match exactly one expression. When used on the consequent side, they stand in for the matched expression. If a slot variable appears twice in a matcher pattern, all corresponding matches must be equal (as tested by `Base.isequal` function). Hence this rule says: if you see something added to itself, make it twice of that thing, and works as such.

If you try to apply this rule to an expression where the two summands are not equal, it will return `nothing` -- this is the way a rule signifies failure to match.
```julia:rewrite2
r1(sin(1+z) + sin(1+w)) === nothing
```

If you want to match a variable number of subexpressions at once, you will need a **segment variable**. `~~xs` in the following example is a segment variable:

```julia:rewrite3
@syms x y z
@rule(+(~~xs) => ~~xs)(x + y + z)
```

`~~xs` is a vector of subexpressions matched. You can use it to construct something more useful:

```julia:rewrite4
r2 = @rule ~x * +(~~ys) => sum(map(y-> ~x * y, ~~ys));

r2(2 * (w+w+α+β))
```

Notice that there is a subexpression `(2 * w) + (2 * w)` that could be simplified by the previous rule `r1`. Can we chain `r2` and `r1`?


### Predicates for matching

Matcher pattern may contain slot variables with attached predicates, written as `~x::f` where `f` is a function that takes a matched expression and returns a boolean value. Such a slot will be considered a match only if `f` returns true.

Similarly `~~x::g` is a way of attaching a predicate `g` to a segment variable. In the case of segment variables `g` gets a vector of 0 or more expressions and must return a boolean value. If the same slot or segment variable appears twice in the matcher pattern, then at most one of the occurance should have a predicate.

For example,

```julia:pred1

r = @rule ~x + ~~y::(ys->iseven(length(ys))) => "odd terms"

@show r(w + z + z + w)
@show r(w + z + z)
@show r(w + z)
```


### Associative-Commutative Rules

Given an expression `f(x, f(y, z, u), v, w)`, a `f` is said to be associative if the expression is equivalent to `f(x, y, z, u, v, w)` and commutative if the order of arguments does not matter.  SymbolicUtils has a special `@acrule` macro meant for rules on functions which are associate and commutative such as addition and multiplication of real and complex numbers.

```julia:acr
@syms x y

acr = @acrule((~y)^(~n) * ~y => (~y)^(~n+1))

acr(x^2 * y * x)
```


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
   returns true, `rw2` if it retuns false
- `If(cond, rw)` is the same as `IfElse(cond, rw, Empty())`
- `Prewalk(rw; threaded=false, thread_cutoff=100)` returns a rewriter which does a pre-order
   traversal of a given expression and applies the rewriter `rw`. `threaded=true` will
   use multi threading for traversal. `thread_cutoff` is the minimum number of nodes
   in a subtree which should be walked in a threaded spawn.
- `Postwalk(rw; threaded=false, thread_cutoff=100)` similarly does post-order traversal.
- `Fixpoint(rw)` returns a rewriter which applies `rw` repeatedly until there are no changes to be made.
- `PassThrough(rw)` returns a rewriter which if `rw(x)` returns `nothing` will instead
   return `x` otherwise will return `rw(x)`.


Example using Postwalk, and Chain

```julia:rewrite6

using SymbolicUtils
using SymbolicUtils.Rewriters

r1 = @rule ~x + ~x => 2 * (~x)
r2 = @rule ~x * +(~~ys) => sum(map(y-> ~x * y, ~~ys));

rset = Postwalk(Chain([r1, r2]))
rset_result = rset(2 * (w+w+α+β))

rset_result
```

It applied `r1`, but didn't get the opportunity to apply `r2`. So we need to apply the ruleset again on the result.

```julia:rewrite7
rset(rset_result)
```

You can also use `Fixpoint` to apply the rules until there are no changes.
```julia:rewrite8
Fixpoint(rset)(2 * (w+w+α+β))
```
