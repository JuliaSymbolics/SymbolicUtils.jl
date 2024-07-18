"""
$(DocStringExtensions.README)
"""
module SymbolicUtils

using DocStringExtensions

export @syms, term, showraw, hasmetadata, getmetadata, setmetadata

using Unityper
using TermInterface
using DataStructures
using Setfield
import Setfield: PropertyLens
using SymbolicIndexingInterface
import Base: +, -, *, /, //, \, ^, ImmutableDict
using ConstructionBase
using TermInterface
import TermInterface: iscall, isexpr, head, children,
                      operation, arguments, metadata, maketerm, sorted_arguments

Base.@deprecate istree iscall
export istree, operation, arguments, sorted_arguments, similarterm, iscall
# Sym, Term,
# Add, Mul and Pow
include("types.jl")

# Methods on symbolic objects
using SpecialFunctions, NaNMath
import IfElse: ifelse  # need to not bring IfElse name in or it will clash with Rewriters.IfElse
include("methods.jl")

# LinkedList, simplification utilities
include("utils.jl")

# Tree inspection
include("inspect.jl")
export Rewriters

# A library for composing together expr -> expr functions

using Combinatorics: permutations, combinations
export @rule, @acrule, RuleSet

# Rule type and @rule macro
include("rule.jl")
include("matchers.jl")
include("rewriters.jl")

# Convert to an efficient multi-variate polynomial representation
import MultivariatePolynomials as MP
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

include("code.jl")


# Adjoints
include("adjoints.jl")

end # module
