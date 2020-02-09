export @vars

"""
    Variable(name[, domain=Number])

A named variable with an optional domain.
domain defaults to number.
"""
struct Variable
    name::Symbol
    domain
end

Base.convert(::Type{Expr}, v::Variable) = v.name

Base.show(io::IO, v::Variable) = print(io, v.name, "::", v.domain)

Variable(x) = Variable(x, Number)

domain(v::Variable) = v.domain

_name(x::Symbol) = x
function _name(x::Expr)
    x.head === :(::) || error("variable definition syntax is name::Type")
    x.args[1]
end
_domain(x::Symbol) = Number
function _name(x::Expr)
    x.head === :(::) || error("variable definition syntax is name::Type")
    x.args[2]
end

macro vars(xs...)
    lhs = Expr(:tuple, map(_name, xs)...)
    vars = map(xs) do x
        :(Variable($(Expr(:quote, _name(x))),
                   $(esc(_domain(x)))))
    end
    :($(esc(lhs)) = ($(vars...),))
end

# TODO: Allow variables to be declared as functions.
# e.g. literal-function
(::Variable)(args...) = error("Variables are not callable.")
