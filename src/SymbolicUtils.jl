"""
$(DocStringExtensions.README)
"""
module SymbolicUtils

using DocStringExtensions
export @syms, term, showraw, hasmetadata, getmetadata, setmetadata

using TermInterface
using TermInterface: node_count
using Metatheory
using Metatheory.Rules
using Metatheory.Rewriters
using Unityper

# Sym, Term,
# Add, Mul and Pow
using DataStructures
using Setfield
import Setfield: PropertyLens
import Base: +, -, *, /, //, \, ^, ImmutableDict
using ConstructionBase
include("types.jl")
export istree, operation, arguments, similarterm

# Methods on symbolic objects
using SpecialFunctions, NaNMath
import IfElse: ifelse  # need to not bring IfElse name in or it will clash with Rewriters.IfElse
include("methods.jl")

# LinkedList, simplification utilities
include("utils.jl")

export Rewriters

# A library for composing together expr -> expr functions

using Combinatorics: permutations, combinations
export @rule, @acrule, RuleSet

# Rule type and @rule macro
include("rule.jl")

# Convert to an efficient multi-variate polynomial representation
import MultivariatePolynomials
const MP = MultivariatePolynomials
import DynamicPolynomials
export expand
include("polyform.jl")

# Term ordering
include("ordering.jl")

# Default rules for expression simplification
include("simplify_rules.jl")

# API = simplify + substitute
export simplify
include("simplify.jl")

export substitute
include("substitute.jl")

# EGraph rewriting
include("egraph.jl")
export optimize

include("code.jl")


# ADjoints
include("adjoints.jl")

end # module
