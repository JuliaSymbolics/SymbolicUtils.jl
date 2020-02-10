symtype(x) = typeof(x) # For types outside of SymbolicUtils

@noinline function promote_symtype(f, xs...)
    error("promote_symtype($f, $(join(xs, ", "))) not defined")
end

termstyle(f, ds...) = AC{false,false}()
termstyle(f::typeof(+), ds...) = AC{true,true}()
termstyle(f::typeof(*), ds::Type{<:Union{Real,Complex}}...) = AC{true,true}()
termstyle(f::typeof(*), ds::Type{<:Number}...) = AC{true,false}()
termstyle(f::typeof(*), ds::Type{<:AbstractArray}...) = AC{true,false}()

# Associative and/or commutative?
struct AC{A, C} end

struct Term{C}
    style::Any
    f::Any
    type::Any
    arguments::C # A collection of Term=>multiplicity pairs
end

function term(style::AC, f, args...; type = nothing)

    if type === nothing
        t = promote_symtype(f, map(symtype, args)...)
    else
        t = type
    end

    maketerm(style, f, t, args)
end
term(f, args...; type=nothing) = term(AC{false,false}(), f, args...; type=type)

operation(x::Term) = x.f
symtype(x::Term)   = x.type
termstyle(x::Term) = x.style

function arguments(x::Term)
    if termstyle(x) === AC{false, false}()
        (a=>1 for a in x.arguments)
    else
        x.arguments
    end
end

# AC{true, true}: store arguments as a dictionary
# while flattening any AC{true, true} type arguments which might have the same f
function maketerm(t::AC{true, true}, f, d, args)
    if length(args) == 0
        dict = pdict{Any, UInt}()
        rest = ()
    elseif termstyle(first(args)) isa AC{true, true} && operation(first(args)) === f
        dict = arguments(first(args))
        rest = Iterators.drop(args, 1)
    else
        dict = pdict{Any, UInt}()
        rest = args
    end

    for arg ∈ rest
        if termstyle(arg) isa AC{true, true} && operation(arg) == f
            d = promote_symtype(f, symtype(arg), d)

            # Flatten and add multiplicity if arguments repeat
            dict = pdict_merge(+, dict, arguments(arg))
        else
            # Do not flatten, leave term as it is
            d = promote_symtype(f, symtype(arg), d)
            # TODO: do one less lookup
            dict = assoc(dict, arg, get(dict, arg, 0) + 1)
        end
    end

    return Term(t, f, d, dict)
end

# AC{false, false}: store arguments as vector of any
function maketerm(t::AC{false, false}, f, d, args)
    return Term(t, f, d, Any[args...])
end
