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


function match_literal(val)
    function literal_matcher(data, bindings, next)
        isequal(car(data), val) && next(bindings, 1)
    end
end

function match_slot(slot)
    function slot_matcher(data, bindings, next)
        if haskey(bindings, slot.name) # Namedtuple?
            isequal(bindings[slot.name], car(data)) && next(bindings, 1)
        else
            if slot.predicate(car(data))
                next(assoc(bindings, slot.name, car(data)), 1)
            end
        end
    end
end

function trymatchexpr(data, value, n)
    if isempty(value)
        return n
    elseif islist(value) && islist(data)
        if isempty(data)
            # didn't fully match
            return 0
        end

        while isequal(car(value), car(data))
            n += 1
            value = cdr(value)
            data = cdr(data)
            if isempty(value)
                return n
            elseif isempty(data)
                return 0
            end
        end
        return isempty(value) ? n : 0
    elseif isequal(value, data)
        return n + 1
    end
end

@inline function take_n(ll, n)
    if isempty(ll) || n == 0
        return ()
    else
        (car(ll), take_n(cdr(ll), n-1)...,)
    end
end

function match_segment(segment)
    function segment_matcher(data, bindings, success)
        if haskey(bindings, segment.name)
            n = trymatchexpr(data, bindings[segment.name], 0)
            if n > 0
                success(bindings, n)
            end
        else
            # create a new match
            for i=0:length(data)
                subexpr = take_n(data, i)
                if segment.predicate(subexpr)
                    res = success(assoc(bindings, segment.name, subexpr), i)
                    if res !== false
                        break
                    end
                end
            end
        end
    end
end

