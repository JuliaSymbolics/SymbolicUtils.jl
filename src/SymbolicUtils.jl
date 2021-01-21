module SymbolicUtils

export @syms, term, showraw

# Sym, Term,
# Add, Mul and Pow
using DataStructures
import Base: +, -, *, /, \, ^
include("types.jl")

# Methods on symbolic objects
using SpecialFunctions, NaNMath
export cond
include("methods.jl")

# LinkedList, simplification utilities
include("utils.jl")

export Rewriters

# A library for composing together expr -> expr functions
include("rewriters.jl")

using .Rewriters

using Combinatorics: permutations, combinations
export @rule, @acrule, RuleSet

# Rule type and @rule macro
include("rule.jl")

# Matching a Rule
include("matchers.jl")


# Term ordering
include("ordering.jl")


end # module
