using Documenter
using Pkg
using Test
using SymbolicUtils
using ReferenceTests
import IfElse: ifelse

DocMeta.setdocmeta!(
    SymbolicUtils,
    :DocTestSetup,
    :(using SymbolicUtils);
    recursive=true
)

# Only test one Julia version to avoid differences due to changes in printing.
if v"1.10" ≤ VERSION < v"1.11-"
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
    # Disabled until https://github.com/JuliaMath/SpecialFunctions.jl/issues/446 is fixed
    include("fuzz.jl")
    include("adjoints.jl")
end
