module SymbolicUtils

const TIMER_OUTPUTS = true

if TIMER_OUTPUTS
    using TimerOutputs

    macro timer(name, expr)
        :(@timeit $name $expr) |> esc
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

abstract type Symbolic{T} end

symtype(x) = typeof(x) # For types outside of SymbolicUtils
symtype(::Symbolic{T}) where {T} = T

@noinline function promote_symtype(f, xs...)
    error("promote_symtype($f, $(join(xs, ", "))) not defined")
end

include("symbolic.jl")
include("methods.jl")
include("util.jl")
include("rewrite.jl")
include("simplify.jl")

end # module
