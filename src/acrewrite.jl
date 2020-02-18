struct ACRule
    rule::Rule
    arity::Int
end

function Base.getproperty(acr::ACRule, s::Symbol)
    if s ∈ fieldnames(Rule)
        getproperty(acr.rule, s)
    else
        getfield(acr, s)
    end
end

Base.propertynames(r::ACRule) = (:rule, :expr, :lhs, :rhs, :depth, :_init_matches)

Rule(acr::ACRule) = acr.rule

macro acrule(expr)
    arity = length(expr.args[2].args[2:end])
    quote
        ACRule(@rule($expr), $arity)
    end
end

Base.show(io::IO, acr::ACRule) = print(io, "ACRule(", acr.rule, ")")

function rewriter(acrule::ACRule)
    r = (rewriter ∘ Rule)(acrule)
    function acrule_rewriter(term)
        if term isa Variable
            r(term)
        else
            f =  operation(term)
            f == operation(acrule.lhs) || return nothing
            
            T = symtype(term)
            args = arguments(term)
            
            for inds in permutations(eachindex(args), acrule.arity)
                result = r(Term(f, T, args[inds]))
                if !isnothing(result)
                    return Term(f, T, [result, (args[i] for i in eachindex(args) if i ∉ inds)...])
                end
            end
        end
    end
end
