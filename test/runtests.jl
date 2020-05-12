using Test
using SymbolicUtils

# == / != syntax is nice, let's use it in tests
macro eqtest(expr)
    @assert expr.head == :call && expr.args[1] in [:(==), :(!=)]
    if expr.args[1] == :(==)
        :(@test isequal($(expr.args[2]), $(expr.args[3])))
    else
        :(@test !isequal($(expr.args[2]), $(expr.args[3])))
    end |> esc
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
