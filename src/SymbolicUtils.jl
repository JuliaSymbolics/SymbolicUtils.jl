"""
$(DocStringExtensions.README)
"""
module SymbolicUtils

using DocStringExtensions

export @syms, term, showraw, hasmetadata, getmetadata, setmetadata

using Moshi.Data: @data
import Moshi.Data as MData
using Moshi.Match: @match
using EnumX: @enumx
using TermInterface
using Setfield
import Setfield: PropertyLens
using SymbolicIndexingInterface
import Base: +, -, *, /, //, \, ^, ImmutableDict
using ConstructionBase
using TermInterface
import TermInterface: iscall, operation, arguments, metadata, maketerm, sorted_arguments
# For ReverseDiffExt
import ArrayInterface
import ExproniconLite as EL
import TaskLocalValues: TaskLocalValue
using WeakCacheSets: WeakCacheSet, getkey!
using Base: RefValue
import MacroTools
import PrecompileTools
PrecompileTools.@recompile_invalidations begin
    import MultivariatePolynomials as MP
    import DynamicPolynomials as DP
    import MutableArithmetics as MA
    import SparseArrays: SparseMatrixCSC, findnz, sparse
    using DataStructures
    using ReadOnlyArrays
end
import LinearAlgebra

macro manually_scope(val, expr, is_forced = false)
    @assert Meta.isexpr(val, :call)
    @assert val.args[1] == :(=>)

    var_name = val.args[2]
    new_val = val.args[3]
    old_name = gensym(:old_val)
    cur_name = gensym(:cur_val)
    retval_name = gensym(:retval)
    close_expr = :($var_name[] = $old_name)
    interpolated_expr = MacroTools.postwalk(expr) do ex
        if Meta.isexpr(ex, :$) && length(ex.args) == 1 && ex.args[1] == :$
            return cur_name
        else
            return ex
        end
    end
    basic_result = quote
        $cur_name = $var_name[] = $new_val
        $retval_name = try
            $interpolated_expr
        finally
            $close_expr
        end
    end
    is_forced && return quote
        $old_name = $var_name[]
        $basic_result
    end |> esc

    return quote
        $old_name = $var_name[]
        if $iszero($old_name)
            $basic_result
        else
            $cur_name = $old_name
            $retval_name = begin
                $interpolated_expr
            end
        end
        $retval_name
    end |> esc
end

# copied from https://github.com/JuliaLang/julia/blob/80f7db8e51b2ba1dd21e913611c23a6d5b75ecab/base/lock.jl#L371-L381
# and adapted for readlock/readunlock
macro readlock(l, expr)
    quote
        temp = $(esc(l))
        $readlock(temp)
        try
            $(esc(expr))
        finally
            $readunlock(temp)
        end
    end
end

include("cache.jl")
Base.@deprecate istree iscall

include("small_array.jl")

export istree, operation, arguments, sorted_arguments, iscall, unwrap_const
# Sym, Term,
# Add, Mul and Pow
PrecompileTools.@recompile_invalidations begin
    include("types.jl")
end

include("printing.jl")

export BS
include("syms.jl")
export @arrayop
include("arrayop.jl")

# Methods on symbolic objects
PrecompileTools.@recompile_invalidations begin
using SpecialFunctions, NaNMath
include("methods.jl")
end
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

include("rule2.jl")

# Convert to an efficient multi-variate polynomial representation
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

PrecompileTools.@recompile_invalidations begin
    include("despecialize.jl")
end

PrecompileTools.@setup_workload begin
    fold1 = Val{false}()
    fold2 = Val{true}()
    PrecompileTools.@compile_workload begin
        @syms x y f(t) q[1:5]
        Sym{SymReal}(:a; type = Real, shape = ShapeVecT())
        x + y
        x * y
        x / y
        x ^ y
        x ^ 5
        6 ^ x
        x - y
        -y
        2y
        symtype(y)
        f(x)
        (5x / 5)
        z = 2
        x ^ z
        Const{SymReal}(x; unsafe=true)
        show(devnull, x ^ 2 + y * x + y / 3x)
        expand((x + y) ^ 2)
        simplify(x ^ (1//2) + (sin(x) ^ 2 + cos(x) ^ 2) + 2(x + y) - x - y)
        ex = x + 2y + sin(x)
        rules1 = Dict(x => y)
        rules2 = Dict(x => 1)
        # Running `fold = Val(true)` invalidates the precompiled statements
        # for `fold = Val(false)` and itself doesn't precompile anyway.
        substitute(ex, rules1)
        # substitute(ex, rules1; fold = fold1)
        # substitute(ex, rules2; fold = fold1)
        # substitute(ex, rules2)
        # substitute(ex, rules1; fold = fold2)
        # substitute(ex, rules2; fold = fold2)
        q[1]
        q'q
    end
end

end # module
