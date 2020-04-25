
abstract type AbstractRule end # Currently doesn't really do anything. Can be removed.

#-----------------------------
#### Regular Rewriting Rules

struct Rule{L, M, R} <: AbstractRule
    expr::Expr               # rule pattern stored for pretty printing
    lhs::L                   # the pattern
    matcher::M               # matcher(lhs)
    rhs::R                   # consequent
    depth::Int               # number of levels of expr this rule touches
    _init_matches::MatchDict # empty dictionary with the required fields set to nothing, see MatchDict
end

getdepth(r::Rule) = r.depth

function rule_depth(rule, d=0, maxdepth=0)
    if rule isa Term
        maxdepth = maximum(rule_depth(r, d+1, maxdepth) for r in arguments(rule))
    elseif rule isa Slot || rule isa Segment
        maxdepth = max(d, maxdepth)
    end
    return maxdepth
end

function Base.show(io::IO, r::Rule)
    Base.print(io, r.expr)
end

function (r::Rule)(term)
    m, rhs, dict = r.matcher, r.rhs, r._init_matches
    m((term,), dict, (d, n) -> n == 1 ? (@timer "RHS" rhs(d)) : nothing)
end

macro rule(expr)
    @assert expr.head == :call && expr.args[1] == :(=>)
    lhs,rhs = expr.args[2], expr.args[3]
    keys = Symbol[]
    lhs_term = makepattern(lhs, keys)
    unique!(keys)
    dict = matchdict(keys)
    quote
        lhs_pattern = $(lhs_term)
        Rule($(QuoteNode(expr)),
             lhs_pattern,
             matcher(lhs_pattern),
             __MATCHES__ -> $(makeconsequent(rhs)),
             rule_depth($lhs_term),
             $dict)
    end
end

#-----------------------------
#### Associative Commutative Rules

struct ACRule{L, M, R} <: AbstractRule
    rule::Rule{L, M, R}
    arity::Int
end

Rule(acr::ACRule)   = acr.rule
getdepth(r::ACRule) = getdepth(r.rule)

macro acrule(expr)
    arity = length(expr.args[2].args[2:end])
    quote
        ACRule(@rule($expr), $arity)
    end
end

Base.show(io::IO, acr::ACRule) = print(io, "ACRule(", acr.rule, ")")

function (acr::ACRule)(term)
    r = Rule(acr)
    if term isa Variable
        r(term)
    else
        f =  operation(term)
        # Assume that the matcher was formed by closing over a term
        if f != operation(r.lhs) # Maybe offer a fallback if m.term errors. 
            return nothing
        end
        
        T = symtype(term)
        args = arguments(term)
        
        for inds in permutations(eachindex(args), acr.arity)
            result = r(Term{T}(f, args[inds]))
            if !isnothing(result)
                return Term{T}(f, [result, (args[i] for i in eachindex(args) if i ∉ inds)...])
            end
        end
    end
end

#-----------------------------
#### Rulesets

struct RuleSet <: AbstractRule
    rules::Vector{AbstractRule}
end

function (r::RuleSet)(term, depth=-1)
    rules = r.rules
    # simplify the subexpressions
    if depth == 0
        return term
    end
    if term isa Symbolic
        if term isa Term
            expr = Term{symtype(term)}(operation(term),
                        map(t -> r(t, max(-1, depth-1)), arguments(term)))
        else
            expr = term
        end
        for i in 1:length(rules)
            expr′ = try
                @timer(repr(rules[i]), rules[i](expr))
            catch err
                show_rule_error(rules[i], expr)
                rethrow()
            end
            if expr′ === nothing
                # this rule doesn't apply
                continue
            else
                return r(expr′, getdepth(rules[i]) + 1) # levels touched
            end
        end
    else
        expr = term
    end
    return expr # no rule applied
end

@noinline function show_rule_error(rule, expr)
    msg = "\nFailed to apply rule $(rule) on expression "
    msg *= sprint(io->showraw(io, expr))
    Base.showerror(stderr, ErrorException(msg), backtrace()[1:min(100, end)])
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
