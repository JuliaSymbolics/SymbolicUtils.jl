symtype(x) = typeof(x) # For types outside of SymbolicUtils

@noinline function promote_symtype(f, xs...)
    error("promote_symtype($f, $(join(xs, ", "))) not defined")
end

struct Term <: Symbolic
    f::Any
    type::Type
    arguments::Any
end

operation(x::Term) = x.f
symtype(x::Term)   = x.type
termstyle(x::Term) = x.style

function term(f, args...; type = nothing)
    if type === nothing
        t = promote_symtype(f, map(symtype, args)...)
    else
        t = type
    end

    Term(f, t, args)
end

function arguments(x::Term)
    if termstyle(x) === AC{false, false}()
        (a=>1 for a in x.arguments)
    else
        x.arguments
    end
end
