module SymbolicUtils

export @syms, term, @fun, showraw
include("types.jl")


using SpecialFunctions, NaNMath
export cond
include("methods.jl")

include("arrays.jl")

include("util.jl")

export <ₑ
include("term_order.jl")

include("matchers.jl")

using Combinatorics: permutations
export @rule, @acrule, RuleSet
include("rule_dsl.jl")

export simplify, substitute

include("simplify.jl")

include("rulesets.jl")

include("trace.jl")

end # module
