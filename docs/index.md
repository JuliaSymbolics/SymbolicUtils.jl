@def title = "SymbolicUtils.jl — Symbolic programming in Julia"
@def hasmath = false
@def hascode = true
<!-- Note: by default hasmath == true and hascode == false. You can change this in
the config file by setting hasmath = false for instance and just setting it to true
where appropriate -->

# User Manual

[**SymbolicUtils**](https://github.com/JuliaSymbolics/SymbolicUtils.jl) is an practical symbolic programming utility written in Julia. It lets you [create](#symbolic_expressions), [rewrite](#rule-based_rewriting) and [simplify](#simplification) symbolic expressions.


The main features are:

- Symbols (`Sym`s) carry type information. ([read more](#symbolic_expressions))
- Compound expressions composed of `Sym`s propagate type information. ([read more](#symbolic_expressions))
- A flexible [rule-based rewriting language](#rule-based_rewriting) allowing liberal use of user defined matchers and rewriters.
- A [combinator library](#composing-rewriters) for making rewriters.
- Set of [simplification rules](#simplification). These can be remixed and extended for special purposes.


## Table of contents

\tableofcontents <!-- you can use \toc as well -->

## Symbolic expressions

First, let's use the `@syms` macro to create a few symbols.

```julia:syms1
using SymbolicUtils

@syms w z α::Real β::Real

(w, z, α, β) # hide

```
\out{syms1}

Type annotations are optional when creating symbols. Here `α`, `β` behave like Real numbers. `w` and `z` behave like `Number`, which is the default. You can use the `symtype` function to find the type of a symbol.

```julia:symtype
using SymbolicUtils: symtype

symtype(w), symtype(z),  symtype(α), symtype(β)
```
\out{symtype}

Note however that they are not subtypes of these types!

```julia:symtype2
@show w isa Number
@show α isa Real
```
\out{symtype2}

(see [this post](https://discourse.julialang.org/t/ann-symbolicutils-jl-groundwork-for-a-symbolic-ecosystem-in-julia/38455/13?u=shashi) for why they are all not just subtypes of `Number`)

You can do basic arithmetic on symbols to get symbolic expressions:

```julia:expr
expr1 = α*sin(w)^2 +  β*cos(z)^2
expr2 = α*cos(z)^2 +  β*sin(w)^2

expr1 + expr2
```
\out{expr}

Notice the output is simplified! By default SymbolicUtils simplifies expressions before printing. In the REPL, if an expression was successfully simplified before printing, it will appear in yellow rather than white, as a visual cue that what you are looking at is not the exact datastructure. You can set `SymbolicUtils.show_simplified[] = false` to disable simplification on printing, or call `SymbolicUtils.showraw(expr)` to display an expression without simplification.

```julia:showraw
using SymbolicUtils: showraw

showraw(expr1 + expr2)
```
\out{showraw}

**Function-like symbols**

Symbols can be defined to behave like functions. Both the input and output types for the function can be specified. Any application to that function will only admit either values of those types or symbols of the same `symtype`.

```julia:syms2
using SymbolicUtils
@syms f(x) g(x::Real, y::Real)::Real

f(z) + g(1, α) + sin(w)
```
\out{syms2}


```julia:sym3
g(1, z)
```

\out{sym3}

This does not work since `z` is a `Number`, not a `Real`.

```julia:sym4
g(2//5, g(1, β))
```
\out{sym4}

This works because `g` "returns" a `Real`.

## Rule-based rewriting

Rewrite rules match and transform an expression. A rule is written using either the `@rule` macro or the `@acrule` macro.

Here is a simple rewrite rule:

```julia:rewrite1
r1 = @rule ~x + ~x => 2 * (~x)

showraw(r1(sin(1+z) + sin(1+z)))
```
\out{rewrite1}

The `@rule` macro takes a pair of patterns -- the _matcher_ and the _consequent_ (`@rule matcher => consequent`). If an expression matches the matcher pattern, it is rewritten to the consequent pattern. `@rule` returns a callable object that applies the rule to an expression.

`~x` in the example is what is a **slot variable** named `x`. In a matcher pattern, slot variables are placeholders that match exactly one expression. When used on the consequent side, they stand in for the matched expression. If a slot variable appears twice in a matcher pattern, all corresponding matches must be equal (as tested by `Base.isequal` function). Hence this rule says: if you see something added to itself, make it twice of that thing, and works as such.

If you try to apply this rule to an expression where the two summands are not equal, it will return `nothing` -- this is the way a rule signifies failure to match.
```julia:rewrite2
r1(sin(1+z) + sin(1+w)) === nothing
```
\out{rewrite2}

If you want to match a variable number of subexpressions at once, you will need a **segment variable**. `~~xs` in the following example is a segment variable:

```julia:rewrite3
@syms x y z
@rule(+(~~xs) => ~~xs)(x + y + z)
```
\out{rewrite3}

`~~xs` is a vector of subexpressions matched. You can use it to construct something more useful:

```julia:rewrite4
r2 = @rule ~x * +(~~ys) => sum(map(y-> ~x * y, ~~ys));

showraw(r2(2 * (w+w+α+β)))
```
\out{rewrite4}

Notice that there is a subexpression `(2 * w) + (2 * w)` that could be simplified by the previous rule `r1`. Can we chain `r2` and `r1`?


### Predicates for matching

Matcher pattern may contain slot variables with attached predicates, written as `~x::f` where `f` is a function that takes a matched expression (a `Term` object a `Sym` or any Julia value that is in the expression tree) and returns a boolean value. Such a slot will be considered a match only if `f` returns true.

Similarly `~~x::g` is a way of attaching a predicate `g` to a segment variable. In the case of segment variables `g` gets a vector of 0 or more expressions and must return a boolean value. If the same slot or segment variable appears twice in the matcher pattern, then at most one of the occurance should have a predicate.

For example,

```julia:pred1

r = @rule ~x + ~~y::(ys->iseven(length(ys))) => "odd terms"

@show r(w + z + z + w)
@show r(w + z + z)
@show r(w + z)
```

\out{pred1}

### Associative-Commutative Rules

Given an expression `f(x, f(y, z, u), v, w)`, a `f` is said to be associative if the expression is equivalent to `f(x, y, z, u, v, w)` and commutative if the order of arguments does not matter.  SymbolicUtils has a special `@acrule` macro meant for rules on functions which are associate and commutative such as addition and multiplication of real and complex numbers.

```julia:acr
@syms x y

acr = @acrule((~y)^(~n) * ~y => (~y)^(~n+1))

acr(x^2 * y * x)
```
\out{acr}


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
- `Prewalk(rw; threaded=false, thread_cutoff=100)` returns a rewriter which does a pre-order
   traversal of a given expression and applies the rewriter `rw`. `threaded=true` will
   use multi threading for traversal. `thread_cutoff` is the minimum number of nodes
   in a subtree which should be walked in a threaded spawn.
- `Postwalk(rw; threaded=false, thread_cutoff=100)` similarly does post-order traversal.
- `IfElse(cond, rw1, rw2)` runs the `cond` function on the input, applies `rw1` if cond
   returns true, `rw2` if it retuns false
- `If(cond, rw)` is the same as `IfElse(cond, rw, Empty())`
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

showraw(rset_result)
```
\out{rewrite6}

It applied `r1`, but didn't get the opportunity to apply `r2`. So we need to apply the ruleset again on the result.

```julia:rewrite7
showraw(rset(rset_result))
```
\out{rewrite7}
## Simplification

The `simplify` function applies a built-in set of rules to simplify expressions.

```julia:simplify1
showraw(simplify(2 * (w+w+α+β + sin(z)^2 + cos(z)^2 - 1)))
```
\out{simplify1}

If you read the previous section on the rules DSL, you should be able to read and understand the [rules](https://github.com/JuliaSymbolics/SymbolicUtils.jl/blob/master/src/simplify_rules.jl) that are used by `simplify`.

## Learn more

If you have a package that you would like to utilize rule-based rewriting in, look at the suggestions in the [Interfacing](/interface/) section to find out how you can do that without any fundamental changes to your package. Look at the [API documentation](/api/) for docstrings about specific functions or macros.

Head over to the github repository to ask questions and [report problems](https://github.com/JuliaSymbolics/SymbolicUtils.jl)! Join the [Zulip stream](https://julialang.zulipchat.com/#narrow/stream/236639-symbolic-programming) to chat!

