using Test
using SymbolicUtils

# == syntax is nice, but we can't use it because
# it returns a Term{Bool}
macro eqtest(expr)
    @assert expr.hear == :call && expr.args[1] == :(==)
    :(@test isequal($(expr.args[2]), $(expr.args[3]))) |> esc
end
SymbolicUtils.show_simplified[] = false

#using SymbolicUtils: Rule

include("basics.jl")
include("order.jl")
include("rewrite.jl")
include("rulesets.jl")
include("interface.jl")
include("fuzz.jl")
if haskey(ENV, "TRAVIS")
    include("benchmark.jl")
end
