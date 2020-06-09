module SymbolicUtils

const TIMER_OUTPUTS = true
const being_timed = Ref{Bool}(false)

if TIMER_OUTPUTS
    using TimerOutputs

    macro timer(name, expr)
        :(if being_timed[]
              @timeit $(esc(name)) $(esc(expr))
          else
              $(esc(expr))
          end)
    end

    macro iftimer(expr)
        esc(expr)
    end

else
    macro timer(name, expr)
        esc(expr)
    end

    macro iftimer(expr)
    end
end

export @syms, term, @fun, showraw
include("types.jl")


using SpecialFunctions, NaNMath
export cond
include("methods.jl")


include("util.jl")

include("matchers.jl")

using Combinatorics: permutations
export @rule, @acrule, RuleSet
include("rule_dsl.jl")

export simplify, substitute

include("simplify.jl")

include("rulesets.jl")

include("trace.jl")

end # module
