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


export @vars, term, @fun, showraw
include("symbolic.jl")


using SpecialFunctions, NaNMath
include("methods.jl")


include("util.jl")

using Combinatorics: permutations
export @rule, rewriter, @acrule
include("rewrite.jl")

include("acrewrite.jl")


export simplify
include("simplify.jl")


include("rulesets.jl")

end # module
