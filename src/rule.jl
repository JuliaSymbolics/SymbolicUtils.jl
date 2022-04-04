# Matcher patterns with Slot and Segment

#const EMPTY_DICT = ImmutableDict{Symbol, Any}(:____, nothing)



getdepth(::Any) = typemax(Int)


Base.@deprecate RuleSet(x) Postwalk(Chain(x))

struct ACRule{F,R} <: Metatheory.AbstractRule
    sets::F
    rule::R
    arity::Int
end

rule(acr::ACRule)   = acr.rule
getdepth(r::ACRule) = getdepth(r.rule)

macro acrule(expr)
    lhs = arguments(expr)[1]
    arity = length(arguments(lhs)[1:end])
    quote
        ACRule(permutations, $(esc(:(@rule($(expr))))), $arity)
    end
end

macro ordered_acrule(expr)
    lhs = arguments(expr)[1]
    arity = length(arguments(lhs)[1:end])
    quote
        ACRule(combinations, $(esc(:(@rule($(expr))))), $arity)
    end
end

Base.show(io::IO, acr::ACRule) = print(io, "ACRule(", acr.rule, ")")

@inline _nameof(x) = x isa Function ? nameof(x) : x

function (acr::ACRule)(term::Y) where {Y}
    r = rule(acr)
    if !istree(term)
        r(term)
    else
        head = exprhead(term)
        f = operation(term)
        # Assume that the matcher was formed by closing over a term
        if _nameof(f) != _nameof(operation(r.left)) # Maybe offer a fallback if m.term errors. 
            return nothing
        end

        T = symtype(term)
        args = unsorted_arguments(term)

        itr = acr.sets(eachindex(args), acr.arity)

        for inds in itr
            result = r(Term{T}(f, @views args[inds]))
            if result !== nothing
                # Assumption: inds are unique
                length(args) == length(inds) && return result
                return similarterm(Y, f, [result, (args[i] for i in eachindex(args) if i ∉ inds)...], T; exprhead = head)
            end
        end
    end
end
