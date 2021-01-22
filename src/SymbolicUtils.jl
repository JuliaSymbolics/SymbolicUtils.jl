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
export @rule, @acrule, @ordered_acrule, RuleSet

# Rule type and @rule macro
include("rule.jl")

# Matching a Rule
include("matchers.jl")

# Convert to an efficient multi-variate polynomial representation
import AbstractAlgebra.Generic: MPoly, PolynomialRing, ZZ, exponent_vector
using AbstractAlgebra: ismonomial, symbols
include("abstractalgebra.jl")

# Term ordering
include("ordering.jl")

# Default rules for expression simplification
include("simplify_rules.jl")

# API = simplify + substitute
export simplify, substitute
include("api.jl")

end # module
