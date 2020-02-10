export @rule

#### Pattern matching basics

# matches one term
# syntax:  :x
struct Slot{P}
    name::Symbol
    predicate::P
end
Base.isequal(s1::Slot, s2::Slot) = s1.name == s2.name
Base.show(io::IO, s::Slot) = (print(io, "~"); print(io, s.name))

# matches zero or more terms
# syntax: ~x
struct Segment{F}
    name::Symbol
    predicate::F
end

ismatch(s::Segment, t) = s.predicate(t)
_oftype(T) = x->symtype(x)<:T
_oftype(T::Type{<:Tuple}) = x->Tuple{map(symtype, x)...}<:T # used for segments
oftype(T) = _oftype(T)
and(f,g) = x->f(x) && g(x)
or(f,g) = x->f(x) || g(x)
@inline alwaystrue(x) = true

Slot(s) = Slot(s, alwaystrue)
Segment(s) = Segment(s, alwaystrue)

struct Rule
    lhs
    rhs
end

function Base.show(io::IO, r::Rule)
    Base.show(io, r.lhs)
    Base.print(io, "=>")
    Base.show(io, r.rhs)
end

#### Syntactic diabetes

macro rule(expr)
    @assert expr.head == :call && expr.args[1] == :(=>)
    lhs,rhs = expr.args[2], expr.args[3]
    :(Rule($(makepattern(lhs)), __MATCHES__ -> $(@show makeconsequent(rhs))))
end

makesegment(s::Symbol) = Segment(s)
function makesegment(s::Expr)
    if !(s.head == :(::))
        error("Syntax for specifying a segment is ~~x::\$predicate, where predicate is a boolean function")
    end
    name = s.args[1]
    :(Segment($(QuoteNode(name)), $(s.args[2])))
end
makeslot(s::Symbol) = Slot(s)
function makeslot(s::Expr)
    if !(s.head == :(::))
        error("Syntax for specifying a slot is ~x::\$predicate, where predicate is a boolean function")
    end
    name = s.args[1]
    :(Slot($(QuoteNode(name)), $(s.args[2])))
end

struct Pattern end # used as domain type for terms here

function makepattern(expr)
    if expr isa Expr
        if expr.head === :call
            if expr.args[1] === :(~)
                if expr.args[2] isa Expr && expr.args[2].args[1] == :(~)
                    # matches ~~x::predicate
                    return makesegment(expr.args[2].args[2])
                else
                    # matches ~x::predicate
                    return makeslot(expr.args[2])
                end
            else
                return :(term($(map(makepattern, expr.args)...); type=Pattern))
            end
        else
            error("Unsupported Expr of type $(expr.head) found in pattern")
        end
    else
        # treat as a literal
        return expr
    end
end

function makeconsequent(expr)
    if expr isa Expr
        if expr.head === :call
            if expr.args[1] === :(~)
                if expr.args[2] isa Symbol
                    return :(getfield(__MATCHES__, $(QuoteNode(expr.args[2]))))
                elseif expr.args[2] isa Expr && expr.args[2].args[1] == :(~)
                    @assert expr.args[2].args[2]
                    return :(getfield(__MATCHES__, $(QuoteNode(expr.args[2].args[2]))))
                end
            else
                return Expr(:call, map(makeconsequent, expr.args)...)
            end
        else
            error("Unsupported Expr of type $(expr.head) found in pattern")
        end
    else
        # treat as a literal
        return expr
    end
end

# From the book:
#
# (a ~x ~y ~x c)
#
# has many many matches for
#
# (a b b b b b b c)
#
# Ref [42] for research on term rewriting with equational theories
#
# Bidirectional rules are not discussed.
#

function match_literal(val)
    function literal_matcher(data, bindings, next)
        isequal(car(data), val) && next(bindings, 1)
    end
end

function match_slot(slot)
    function slot_matcher(data, bindings, success)
        if haskey(bindings, slot.name) # Namedtuple?
            isequal(bindings[slot.name], car(data)) && next(bindings, 1)
        else
            next(assoc(bindings, slot.name, car(data)), 1)
        end
    end
end

function match_segment(segment)
end
