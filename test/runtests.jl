using Documenter
using Pkg
using Test
using SymbolicUtils
import IfElse: ifelse

DocMeta.setdocmeta!(
    SymbolicUtils,
    :DocTestSetup,
    :(using SymbolicUtils);
    recursive=true
)

# Only test one Julia version to avoid differences due to changes in printing.
if v"1.6" ≤ VERSION < v"1.7-beta3.0"
    doctest(SymbolicUtils)
else
    @warn "Skipping doctests"
end
SymbolicUtils.show_simplified[] = false

include("utils.jl")

if haskey(ENV, "SU_BENCHMARK_ONLY")
    include("benchmark.jl")
else
    include("basics.jl")
    include("order.jl")
    include("polyform.jl")
    include("rewrite.jl")
    include("rulesets.jl")
    include("code.jl")
    include("cse.jl")
    include("interface.jl")
    include("fuzz.jl")
    include("adjoints.jl")
end
