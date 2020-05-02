using Test
using SymbolicUtils

SymbolicUtils.show_simplified[] = false

#using SymbolicUtils: Rule

include("basics.jl")
include("order.jl")
include("rewrite.jl")
include("rulesets.jl")
include("interface.jl")
include("fuzz.jl")

if haskey(ENV, "TRAVIS")
    # A little trick for travis
    using PkgBenchmark

    pkgpath = dirname(dirname(pathof(SymbolicUtils)))
    # move it out of the repository so that you can check out different branches
    script = tempname() * ".jl"
    benchpath = joinpath(pkgpath, "benchmark", "benchmarks.jl")
    cp(benchpath, script)

    j = judge(pkgpath, "master", retune=true, script=script)
    export_markdown(stdout, j, export_invariants=true)
end
