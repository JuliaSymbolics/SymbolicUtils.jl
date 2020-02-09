module SymbolicUtils

using FunctionalCollections
const pdict = PersistentHashMap

include("util.jl")
include("variable.jl")
include("term.jl")

end # module
