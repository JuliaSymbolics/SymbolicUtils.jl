using Test
using SymbolicUtils

SymbolicUtils.show_simplified[] = false

#using SymbolicUtils: Rule

include("basics.jl")
include("order.jl")
include("rewrite.jl")
include("rulesets.jl")
include("fuzz.jl")
