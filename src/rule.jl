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

#-----------------------------
#### Numeric Rules

function expr_to_canon(expr)
    if expr isa Expr
        if expr.head === :call
            if expr.args[1] === :(-)
                if length(expr.args) == 2
                    return :((-1)*$(expr_to_canon(expr.args[2])))
                elseif !(expr.args[3] isa Number)
                    if expr.args[3].args[1] == :*
                        insert!(expr.args[3].args, 2, -1)
                        return :($(expr_to_canon(expr.args[2])) + $(expr_to_canon(expr.args[3])))
                    else
                        return :($(expr_to_canon(expr.args[2])) + (-1)*$(expr_to_canon(expr.args[3])))
                    end
                else
                    if !(expr.args[2] isa Number) && expr.args[2].args[1] == :+
                        insert!(expr.args[2].args, 2, -1)
                        return :($(expr_to_canon(expr.args[2])))
                    else
                        return :($(expr_to_canon(expr.args[2])) + $(-expr.args[3]))
                    end
                end
            elseif expr.args[1] === :(\)
                return expr_to_canon(:($(expr.args[3]) / $(expr.args[2])))
            elseif expr.args[1] === :(//)
                if !(expr.args[3] isa Number) && !(expr.args[3] in [:π, :ℯ, :pi])
                    return expr_to_canon(:($(expr.args[2]) / $(expr.args[3])))
                else #if expr.args[3] isa Integer
                    return expr_to_canon(:($(1//eval(expr.args[3])) * $(expr.args[2])))
                end
            else
                return :($(expr.args[1])($(expr_to_canon.(expr.args[2:end])...)))
            end
        end
    else
        # treat as a literal
        return expr
    end
end

macro numrule(expr)
    @assert expr.head == :call && expr.args[1] == :(=>)
    lhs,rhs = expr.args[2], expr.args[3]
    lhs = expr_to_canon(lhs)
    expr = :($lhs => $rhs)
    quote
        $(esc(:(@rule($(expr)))))
    end
end
