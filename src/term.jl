domain(x) = typeof(x) # For types outside of SymbolicUtils
promote_domain(f, xs...) = Any

# Associative and/or commutative?
struct AC{A, C} end

struct Term{TType, C}
    f::Any
    domain::Any
    arguments::C # A collection of Term=>multiplicity pairs
end

function term(termtype::AC, f, args...; domain = nothing)

    if domain === nothing
        d = promote_domain(f, map(SymbolicUtils.domain, args)...)
    else
        d = domain
    end

    maketerm(termtype, f, d, args)
end
term(f, args...; domain=nothing) = term(AC{false,false}(), f, args...; domain=domain)

termtype(x::Term{T}) = T()
operation(x::Term) = x.f
domain(x::Term) = x.domain
arguments(x::Term) = x.arguments

# AC{true, true}: store arguments as a dictionary
# while flattening any AC{true, true} type arguments which might have the same f
function maketerm(::AC{true, true}, f, d, args)
    if length(args) == 0
        dict = pdict{Any, UInt}()
        rest = ()
    elseif termtype(first(args)) isa AC{true, true} && operation(first(args)) === f
        dict = arguments(first(args))
        rest = Iterators.drop(args, 1)
    else
        dict = pdict{Any, UInt}()
        rest = args
    end

    for arg ∈ rest
        if termtype(arg) isa AC{true, true} && operation(arg) == f
            d = promote_domain(f, domain(arg), d)

            # Flatten and add multiplicity if arguments repeat
            dict = pdict_merge(+, dict, arguments(arg))
        else
            # Do not flatten, leave term as it is
            d = promote_domain(f, domain(arg), d)
            # TODO: do one less lookup
            dict = assoc(dict, arg, get(dict, arg, 0) + 1)
        end
    end

    return Term{AC{true,true}}(f, d, dict)
end

# AC{false, false}: store arguments as vector of any
function maketerm(::AC{false, false}, f, d, args)
    return Term{AC{false,false}}(f, d, Any[args...])
end

# Special case arguments here to make it an iterator of pairs
arguments(t::Term{AC{false,false}}) = (a=>1 for a in t.arguments)
