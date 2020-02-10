export @rule

#### Pattern matching basics

# matches one term
# syntax:  :x
struct Slot
    name::Symbol
end
Base.isequal(s1::Slot, s2::Slot) = s1.name == s2.name
Base.show(io::IO, s::Slot) = Base.show(io, s.name)

# matches zero or more terms
# syntax: ~x
struct Segment
    name::Symbol
end

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
    :(Rule($(makepattern(lhs)), __MATCHES__ -> $(makeconsequent(rhs))))
end

makesegment(s::Symbol) = Segment(s)
makeslot(s::Symbol) = Slot(s)

struct Pattern end # used as domain type for terms here

function makepattern(expr)
    if expr isa QuoteNode
        return makeslot(expr.value)
    elseif expr isa Expr
        if expr.head === :call
            if expr.args[1] === :(~)
                return makesegment(expr.args[2])
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
    if expr isa QuoteNode
        return :(getfield(__MATCHES__, $(expr)))
    elseif expr isa Expr
        if expr.head === :call
            if expr.args[1] === :(~)
                return :(getfield(__MATCHES__, $(QuoteNode(expr.args[2]))))
            else
                return :(term($(map(makeconsequent, expr.args)...); type=Pattern))
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
    function literal_matcher(data, idx, bindings, success)
        isequal(data[idx], val) && success(bindings, 1)
    end
end

function match_slot(slot)
    function slot_matcher(data, idx, bindings, success)
        if haskey(bindings, slot.name) # Namedtuple?
            isequal(bindings[slot.name], data[idx]) && success(bindings, 1)
        else
            success(assoc(bindings, slot.name, data[idx]), 1)
        end
    end
end

function match_segment(segment)
end
