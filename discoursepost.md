
Hello everyone, we (Shashi Gowda, Yingbo Ma and Mason Protter) are pleased to present to you [SymbolicUtils.jl](https://github.com/JuliaSymbolics/SymbolicUtils.jl). This is the first of hopefully many packages to live in the JuliaSymbolics Github organization, and we hope that SymbolicUtils.jl can lay the groundwork for a vibrant, interacting symbolic programming ecosystem in julia.

Building symbolic programming systems is **hard** and there are various reasons to think it is unlikely that one person, or even a small, coordinated group of people, will be able to to build a monolithic symbolic programming system in Julia that can compete with something like Mathematica or SymPy. Hence, we think it's important to build flexible infrastructure that other's can build on, and interoperate with. Other packages are welcome to build on top of our symbolic types but do not have to. We build extensive infrastructure for [interfacting with SymbolicUtils](https://juliasymbolics.github.io/SymbolicUtils.jl/interface/) so that packages can use their own types if they wish, but plug into our rule rewriting infrastructure.
 
We're happy to say that [ModelingToolkit.jl](https://github.com/SciML/ModelingToolkit.jl/pull/326) from the SciML organization is the first package to depend on and interoperate with SymbolicUtils.jl.

SymbolicUtils.jl is on the general registry and can be added the usual way:
```julia
pkg> add SymbolicUtils
```
or
```julia
julia> using Pkg; pkg"add SymbolicUtils"
```

Here's a quick and unexplained code sample:
```julia
julia> using SymbolicUtils

julia> @syms x::Real y::Real z::Complex f(::Number)::Real
(x, y, z)

julia> 2x^2 - y + x^2
(3 * (x ^ 2)) + (-1 * y)

julia> f(sin(x)^2 + cos(x)^2) + z
f(1) + z

julia> r = @rule sinh(im * ~x) => sin(~x)
sinh(im * ~x) => sin(~x)

julia> r(sinh(im * y))
sin(y)

julia> simplify(cos(y)^2 + sinh(im*y)^2, [r])
1
```
We encourage you to [read the docs](https://juliasymbolics.github.io/SymbolicUtils.jl/) for more info.

Collaboration and documentation improvements / suggestions are quite welcome! If you want to chat about SymbolicUtils.jl, you can find us here, on GitHub, or in the [symbolic programming](https://julialang.zulipchat.com/#narrow/stream/236639-symbolic-programming) Zulip stream.
