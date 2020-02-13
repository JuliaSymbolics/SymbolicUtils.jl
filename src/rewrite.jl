export @rule, rewriter

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

Base.show(io::IO, s::Segment) = (print(io, "~~"); print(io, s.name))

struct Rule
    expr
    lhs
    rhs
    _init_matches
end

function Base.show(io::IO, r::Rule)
    Base.print(io, r.expr)
end

#### Syntactic diabetes

macro rule(expr)
    @assert expr.head == :call && expr.args[1] == :(=>)
    lhs,rhs = expr.args[2], expr.args[3]
    keys = Symbol[]
    lhs_term = makepattern(lhs, keys)
    unique!(keys)
    dict = matchdict(keys)
    :(Rule($(QuoteNode(expr)), $(lhs_term), __MATCHES__ -> $(makeconsequent(rhs)), $dict))
end

makesegment(s::Symbol, keys) = (push!(keys, s); Segment(s))
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
                    return makesegment(expr.args[2].args[2], keys)
                else
                    # matches ~x::predicate
                    return makeslot(expr.args[2], keys)
                end
            else
                return :(term($(map(x->makepattern(x, keys), expr.args)...); type=Any))
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
            return Expr(expr.head, map(makeconsequent, expr.args)...)
        end
    else
        # treat as a literal
        return expr
    end
end


### Matching procedures
# A matcher is a function which takes 3 arguments
# 1. Expression
# 2. Dictionary
# 3. Callback: takes arguments Dictionary × Number of elements matched
#
function matcher(val::Any)
    function literal_matcher(data, bindings, next)
        !isempty(data) && isequal(car(data), val) ? next(bindings, 1) : nothing
    end
end

function matcher(slot::Slot)
    function slot_matcher(data, bindings, next)
        isempty(data) && return
        val = bindings[slot.name]
        if val !== nothing
            if isequal(val, car(data))
                return next(bindings, 1)
            end
        else
            if slot.predicate(car(data))
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
    function segment_matcher(data, bindings, success)
        val = bindings[segment.name]
        if val !== nothing
            n = trymatchexpr(data, val, 0)
            if n !== nothing
                success(bindings, n)
            end
        else
            res = nothing
            for i=length(data):-1:0
                subexpr = take_n(data, i)
                if segment.predicate(subexpr)
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
    function term_matcher(data, bindings, success)
        isempty(data) && return nothing
        !(car(data) isa Term) && return nothing
        function loop(term, bindings′, matchers′) # Get it to compile faster
            if isempty(matchers′)
                if  isempty(term)
                    return success(bindings′, 1)
                end
                return nothing
            end
            res = car(matchers′)(term, bindings′,
                                 (b, n) -> loop(drop_n(term, n), b, cdr(matchers′)))
        end
        loop(car(data), bindings, matchers) # Try to eat exactly one term
    end
end


### Rewriting

function rewriter(rule::Rule)
    m = matcher(rule.lhs)
    rhs = rule.rhs
    dict = rule._init_matches
    function rule_rewriter(term)
        return m((term,), dict,
                 (d, n) -> n == 1 ? (@timer "RHS" rhs(d)) : nothing)
    end
end

function rewriter(rules::Vector)
    compiled_rules = map(rewriter, rules)

    function rewrite(term)
        # simplify the subexpressions
        if term isa Term
            expr = Term(operation(term),
                         symtype(term),
                         map(rewrite, arguments(term)))
            for i in 1:length(compiled_rules)
                @timer repr(rules[i]) expr′ = compiled_rules[i](expr)
                if expr′ === nothing
                    # this rule doesn't apply
                    continue
                else
                    return rewrite(expr′)
                end
            end
        else
            expr = term
        end
        return expr # no rule applied
    end
end

function timerewrite(f)
    if !TIMER_OUTPUTS
        error("timerewrite must be called after enabling " *
              "TIMER_OUTPUTS in the main file of this package")
    end
    reset_timer!()
    being_timed[] = true
    x = f()
    being_timed[] = false
    print_timer()
    println()
    x
end

macro timerewrite(expr)
    :(timerewrite(()->$(esc(expr))))
end
