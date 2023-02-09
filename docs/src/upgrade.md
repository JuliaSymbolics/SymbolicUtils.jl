# Upgrade to SymbolicUtils v1

The version 1 of SymbolicUtils utilizes
[Unityper](https://github.com/YingboMa/Unityper.jl) to speed up the compilation
time. We introduce a new type `BasicSymbolic <: Symbolic` to represent all the
previous types `Sym`, `Term`, `Add`, `Mul`, `Pow` and `Div`. Since
`BasicSymbolic` is a concrete type, checking `x isa Sym` or `x isa Pow` no
longer works. Instead, one should use `issym(x)` or `ispow(x)` to check the
"type" of the expression. Also, note that if one does not need to work on a
specific symbolic representation, `issym(x)` and `isterm(x)` should be replaced
by `x isa Symbolic && !istree(x)` and `istree(x)` to be more generic.
Furthermore, dispatching on `Sym`, `Term`, etc no longer works. Instead, a
function that takes `BasicSymbolic` should check the type of the expression
using a `if` statement to select the right code path.

Although we don't have `Sym`, `Term`, etc in the Julia type system anymore, we
still provide convenient constructors for them. For example, `Sym{Real}(:x)`
would still work. For constructor that takes a collection like `Term`s, we
recommend directly construct `Any` element type constructors like `Term(f,
Any[x1, x2])` to reduce extra memory allocation and compile time.
