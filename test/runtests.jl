using Test
using SymbolicUtils

SymbolicUtils.show_simplified[] = false

#using SymbolicUtils: Rule

# Workaround coverage stats for src/rulesets.jl file.
@eval SymbolicUtils include(joinpath(@__DIR__, "..", "src", "rulesets.jl"))

include("basics.jl")
include("rewrite.jl")
include("rulesets.jl")
include("fuzz.jl")
