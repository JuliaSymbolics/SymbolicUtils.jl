# Term Rewriting

## Rule-based rewriting

Rewrite rules match and transform an expression. A rule is written using either the `@rule` macro or the `@acrule` macro. It creates callable `Rule` object.

Here is a simple rewrite rule, that uses formula for the double angle of the sine function:

```julia:rewrite1
using SymbolicUtils

@syms w z α::Real β::Real

(w, z, α, β) # hide

r1 = @rule sin(2(~x)) => 2sin(~x)*cos(~x)

r1(sin(2z))
```

The `@rule` macro takes a pair of patterns -- the _matcher_ and the _consequent_ (`@rule matcher => consequent`). If an expression matches the matcher pattern, it is rewritten to the consequent pattern. `@rule` returns a callable object that applies the rule to an expression.

`~x` in the example is what is a **slot variable** named `x`. In a matcher pattern, slot variables are placeholders that match exactly one expression. When used on the consequent side, they stand in for the matched expression. If a slot variable appears twice in a matcher pattern, all corresponding matches must be equal (as tested by `Base.isequal` function). Hence this rule says: if you see something added to itself, make it twice of that thing, and works as such.

If you try to apply this rule to an expression with triple angle, it will return `nothing` -- this is the way a rule signifies failure to match.
```julia:rewrite2
r1(sin(3z)) === nothing
```

Slot variable (matcher) is not necessary a single variable

```julia:rewrite3
r1(sin(2*(w-z)))
```

but it must be a single expression

```julia:rewrite4
r1(sin(2*(w+z)*(α+β))) === nothing
```

Rules are of course not limited to single slot variable

```julia:rewrite5
r2 = @rule sin(~x + ~y) => sin(~x)*cos(~y) + cos(~x)*sin(~y);

r2(sin(a + b))
```

If you want to match a variable number of subexpressions at once, you will need a **segment variable**. `~~xs` in the following example is a segment variable:

```julia:rewrite6
@syms x y z
@rule(+(~~xs) => ~~xs)(x + y + z)
```

`~~xs` is a vector of subexpressions matched. You can use it to construct something more useful:

```julia:rewrite7
r3 = @rule ~x * +(~~ys) => sum(map(y-> ~x * y, ~~ys));

r3(2 * (w+w+α+β))
```

Notice that the expression was autosimplified before application of the rule.

```julia:rewrite8
2 * (w+w+α+β)
```



### Predicates for matching

Matcher pattern may contain slot variables with attached predicates, written as `~x::f` where `f` is a function that takes a matched expression and returns a boolean value. Such a slot will be considered a match only if `f` returns true.

Similarly `~~x::g` is a way of attaching a predicate `g` to a segment variable. In the case of segment variables `g` gets a vector of 0 or more expressions and must return a boolean value. If the same slot or segment variable appears twice in the matcher pattern, then at most one of the occurance should have a predicate.

For example,

```julia:pred1
@syms a b c d

r = @rule ~x + ~~y::(ys->iseven(length(ys))) => "odd terms";

@show r(a + b + c + d)
@show r(b + c + d)
@show r(b + c + b)
@show r(a + b)
```


### Associative-Commutative Rules

Given an expression `f(x, f(y, z, u), v, w)`, a `f` is said to be associative if the expression is equivalent to `f(x, y, z, u, v, w)` and commutative if the order of arguments does not matter.  SymbolicUtils has a special `@acrule` macro meant for rules on functions which are associate and commutative such as addition and multiplication of real and complex numbers.

```julia:acr
@syms x y z

acr = @acrule((~a)^(~x) * (~a)^(~y) => (~a)^(~x + ~y))

acr(x^y * x^z)
```

although in case of `Number` it also works with regular `@rule` since autosimplification orders and applies associativity and commutativity to the expression.

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

```julia:rewrite9

using SymbolicUtils
using SymbolicUtils.Rewriters

r1 = @rule ~x + ~x => 2 * (~x)
r2 = @rule ~x * +(~~ys) => sum(map(y-> ~x * y, ~~ys));

rset = Postwalk(Chain([r1, r2]))
rset_result = rset(2 * (w+w+α+β))

rset_result
```

It applied `r1`, but didn't get the opportunity to apply `r2`. So we need to apply the ruleset again on the result.

```julia:rewrite10
rset(rset_result)
```

You can also use `Fixpoint` to apply the rules until there are no changes.
```julia:rewrite11
Fixpoint(rset)(2 * (w+w+α+β))
```
