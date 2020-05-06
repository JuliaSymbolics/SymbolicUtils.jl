#### Pattern matching

@inline alwaystrue(x) = true

# matches one term
# syntax:  ~x
struct Slot{P}
    name::Symbol
    predicate::P
end

Slot(s) = Slot(s, alwaystrue)

Base.isequal(s1::Slot, s2::Slot) = s1.name == s2.name

Base.show(io::IO, s::Slot) = (print(io, "~"); print(io, s.name))

# matches zero or more terms
# syntax: ~~x
struct Segment{F}
    name::Symbol
    predicate::F
end

Segment(s) = Segment(s, alwaystrue)

Base.show(io::IO, s::Segment) = (print(io, "~~"); print(io, s.name))

makesegment(s::Symbol, keys) = (push!(keys, s); Segment(s))

"""
A wrapper for slot and segment predicates which allows them to
take two arguments: the value and a Context
"""
struct Contextual{F}
    f::F
end
(c::Contextual)(args...) = c.f(args...)

ctxcall(f, x, ctx) = f isa Contextual ? f(x, ctx) : f(x)

function makesegment(s::Expr, keys)
    if !(s.head == :(::))
        error("Syntax for specifying a segment is ~~x::\$predicate, where predicate is a boolean function")
    end

    name = s.args[1]

    push!(keys, name)
    :(Segment($(QuoteNode(name)), $(esc(s.args[2]))))
end

makeslot(s::Symbol, keys) = (push!(keys, s); Slot(s))

function makeslot(s::Expr, keys)
    if !(s.head == :(::))
        error("Syntax for specifying a slot is ~x::\$predicate, where predicate is a boolean function")
    end

    name = s.args[1]

    push!(keys, name)
    :(Slot($(QuoteNode(name)), $(esc(s.args[2]))))
end

function makepattern(expr, keys)
    if expr isa Expr
        if expr.head === :call
            if expr.args[1] === :(~)
                if expr.args[2] isa Expr && expr.args[2].args[1] == :(~)
                    # matches ~~x::predicate
                    makesegment(expr.args[2].args[2], keys)
                else
                    # matches ~x::predicate
                    makeslot(expr.args[2], keys)
                end
            else
                :(term($(map(x->makepattern(x, keys), expr.args)...); type=Any))
            end
        else
            error("Unsupported Expr of type $(expr.head) found in pattern")
        end
    else
        # treat as a literal
        return esc(expr)
    end
end

function makeconsequent(expr)
    if expr isa Expr
        if expr.head === :call
            if expr.args[1] === :(~)
                if expr.args[2] isa Symbol
                    return :(getindex(__MATCHES__, $(QuoteNode(expr.args[2]))))
                elseif expr.args[2] isa Expr && expr.args[2].args[1] == :(~)
                    @assert expr.args[2].args[2] isa Symbol
                    return :(getindex(__MATCHES__, $(QuoteNode(expr.args[2].args[2]))))
                end
            else
                return Expr(:call, map(makeconsequent, expr.args)...)
            end
        else
            if expr.head == :macrocall
                if expr.args[1] === Symbol("@ctx")
                    if length(filter(x->!(x isa LineNumberNode), expr.args)) != 1
                        error("@ctx takes no arguments. try (@ctx)")
                    end
                    return :__CTX__
                else
                    return esc(expr)
                end
            end
            return Expr(expr.head, map(makeconsequent, expr.args)...)
        end
    else
        # treat as a literal
        return esc(expr)
    end
end

### Matching procedures
# A matcher is a function which takes 3 arguments
# 1. Expression
# 2. Dictionary
# 3. Callback: takes arguments Dictionary × Number of elements matched
#
function matcher(val::Any)
    function literal_matcher(data, bindings, ctx, next)
        !isempty(data) && isequal(car(data), val) ? next(bindings, 1) : nothing
    end
end

function matcher(slot::Slot)
    function slot_matcher(data, bindings, ctx, next)
        isempty(data) && return
        val = get(bindings, slot.name, nothing)
        if val !== nothing
            if isequal(val, car(data))
                return next(bindings, 1)
            end
        else
            if ctxcall(slot.predicate, car(data), ctx)
                next(assoc(bindings, slot.name, car(data)), 1)
            end
        end
    end
end

# returns n == offset, 0 if failed
function trymatchexpr(data, value, n)
    if isempty(value)
        return n
    elseif islist(value) && islist(data)
        if isempty(data)
            # didn't fully match
            return nothing
        end

        while isequal(car(value), car(data))
            n += 1
            value = cdr(value)
            data = cdr(data)

            if isempty(value)
                return n
            elseif isempty(data)
                return nothing
            end
        end

        return isempty(value) ? n : nothing
    elseif isequal(value, data)
        return n + 1
    end
end

function matcher(segment::Segment)
    function segment_matcher(data, bindings, ctx, success)
        val = get(bindings, segment.name, nothing)

        if val !== nothing
            n = trymatchexpr(data, val, 0)
            if n !== nothing
                success(bindings, n)
            end
        else
            res = nothing

            for i=length(data):-1:0
                subexpr = take_n(data, i)

                if ctxcall(segment.predicate, subexpr, ctx)
                    res = success(assoc(bindings, segment.name, subexpr), i)
                    if res !== nothing
                        break
                    end
                end
            end

            return res
        end
    end
end

function matcher(term::Term)
    matchers = (matcher(operation(term)), map(matcher, arguments(term))...,)
    function term_matcher(data, bindings, ctx, success)

        isempty(data) && return nothing
        !(car(data) isa Term) && return nothing

        function loop(term, bindings′, matchers′) # Get it to compile faster
            if isempty(matchers′)
                if  isempty(term)
                    return success(bindings′, 1)
                end
                return nothing
            end
            res = car(matchers′)(term, bindings′, ctx,
                                 (b, n) -> loop(drop_n(term, n), b, cdr(matchers′)))
        end

        loop(car(data), bindings, matchers) # Try to eat exactly one term
    end
end
