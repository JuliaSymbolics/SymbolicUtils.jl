module SymbolicUtils

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
