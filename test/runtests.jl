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

doctest(SymbolicUtils)
SymbolicUtils.show_simplified[] = false

include("utils.jl")

if haskey(ENV, "SU_BENCHMARK_ONLY")
    include("benchmark.jl")
else
    include("types.jl")
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
