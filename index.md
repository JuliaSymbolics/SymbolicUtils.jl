@def title = "SymbolicUtils.jl -- Symbolic programming in Julia"
@def hasmath = false
@def hascode = true
<!-- Note: by default hasmath == true and hascode == false. You can change this in
the config file by setting hasmath = false for instance and just setting it to true
where appropriate -->

# User Manual

**SymbolicUtils** is an extensible symbolic programming utility written in Julia. It lets you [create](#creating_symbolic_expressions), [rewrite](#rule-based_rewriting) and [simplify](#simplification) symbolic expressions.


\tableofcontents <!-- you can use \toc as well -->


In SymbolicUtils, `Sym`, our equivalent of `Symbol`, can carry type information. Compound expressions composed of `Sym`s propagate this information. A [rule-based rewriting language](#rule-based_rewriting) can be used to find subexpressions that satisfy arbitrary conditions and apply arbitrary transformations on the matches. The library also contains a set of useful [simplification rules](#simplification) for expressions of numeric symbols and numbers. These can be remixed and extended for special purposes.


## Creating symbolic expressions

First, let's use the `@syms` macro to create a few symbols.

```julia:syms1
using SymbolicUtils

@syms w z α::Real β::Real

(w, z, α, β) # hide
```
\out{syms1}

Type annotations are optional when creating symbols. Here `α`, `β` behave like Real numbers. `w` and `z` behave like `Number`, which is the default. You can do basic arithmetic on these to get symbolic expressions:

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

So the simplification in SymbolicUtils is done by a set of rules. We will get into more details about the `simplify` function in the next section, but first, let us look at how you can write a rewrite rule to match and transform an expression.

A rule is written using either the `@rule` macro or the `@acrule` macro.

Here is a simple rewrite rule:

```julia:rewrite1
r1 = @rule ~x + ~x => 2 * (~x)

showraw(r1(sin(1+z) + sin(1+z)))
```
\out{rewrite1}

The `@rule` macro takes a pair of patterns -- the matcher and the consequent (`@rule matcher => consequent`). If an expression matches the matcher pattern, it is rewritten to the consequent pattern. `~x` in the example is what is called a **slot variable** named `x`. In a matcher pattern, slot variables are place holders that match exactly one expression. When used on the consequent side they stand in for the matched expression. If a slot variable appears twice in a matcher pattern, then all corresponding matches must be equal (as tested by `Base.isequal` function). Hence this rule says: if you see something added to itself, make it twice of that thing, and works as such.

If you try to apply this rule to an expression where the two summands are not equal, it will return `nothing` -- this is the way a rule signifies failure to match.
```julia:rewrite2
r1(sin(1+z) + sin(1+w)) === nothing
```
\out{rewrite2}

If you want to match a variable number of subexpressions at once, you will need a **segment variable**. `~~ys` in the following example is a segment variable:

```julia:rewrite2.5
@rule(+(~~xs) => ~~xs)(x + y + z)
```
\out{rewrite2.5}

```julia:rewrite3
r2 = @rule ~x * +(~~ys) => sum(map(y-> ~x * y, ~~ys));

showraw(r2(2 * (w+w+α+β)))
```
\out{rewrite3}

Notice that there is a subexpression `(2 * w) + (2 * w)` that could be simplified by the previous rule `r1`.


```julia:rewrite4
showraw(r1(r2(2 * (w+w+α+β))))
```
\out{rewrite4}

Oops! It didn't work! That is because a rule object created by `@rule` matches the whole expression given to it as input.

There is a much better way of combining multiple rules and apply them to subexpressions recursively. That is the `RuleSet`.

A ruleset is a series of rules that are applied to every subexpression of the tree.

```julia:rewrite5
rset = RuleSet([r1, r2])
rset_result = rset(2 * (w+w+α+β))

showraw(rset_result)
```
\out{rewrite5}

It applied `r1`, but didn't get the opportunity to apply `r2`. So we need to apply the ruleset again on the result.

```julia:rewrite6
showraw(rset(rset_result))
```
\out{rewrite6}

Right on. Since there is no way to know how many times one should apply an `rset`, the package exports a convenient `fixpoint` function that applies the `rset` as many times as there are no changes to the expression.

```julia:rewrite7
using SymbolicUtils: fixpoint

fixpoint(rset, 2 * (w+w+α+β))
```
\out{rewrite7}


### Predicates for matching

Matcher pattern may contain slot variables with attached predicates, written as `~x::f` where `f` is a function that takes a matched expression (a `Term` object a `Sym` or any other Julia value that is in the expression tree) and returns a boolean value. Such a slot will be considered a match only if `f` returns true.

Similarly `~~x::g` is a way of attaching a predicate `g` to a segment variable. In the case of segment variables `g` gets a vector of 0 or more expressions and must return a boolean value.

If the same slot or segment variable appears twice in the matcher pattern, then at most one of the occurance should have a predicate. For example.

```julia:pred1

r = @rule ~x + ~~y::(ys->iseven(length(ys))) => "odd terms"

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

## Simplification

Now that you have learned how to write rewrite rules, you should be able to read and understand these [rules](https://github.com/JuliaSymbolics/SymbolicUtils.jl/blob/master/src/rulesets.jl) that are used by `simplify` to simplify an expression. The rules can be accessed in the vector `SymbolicUtils.SIMPLIFY_RULES`.

```julia:simplify1
showraw(simplify(2 * (w+w+α+β + sin(z)^2 + cos(z)^2 - 1)))
```
\out{simplify1}

`simplify` optionally takes a `rules` argument, a vector of rules to use to simplify instead of the default set. Let's try it with the `r1` and `r2` rules we defined above.


```julia:simplify2
showraw(simplify(2 * (w+w+α+β), [r1,r2]))
```
\out{simplify2}

`simplify` runs through the rules repeatedly until there are no changes to be had. To disable this, you can pass in a `fixpoint=false` keyword argument.

```julia:simplify3
showraw(simplify(2 * (w+w+α+β), [r1,r2], fixpoint=false))
```

\out{simplify3}

## Learn more

If you have a package that you would like to utilize rule-based rewriting in, look at the suggestions in the [Interfacing](/interface/) section.

Head over to the github repository to [report problems](https://github.com/JuliaSymbolics/SymbolicUtils.jl) or ask questions!
