# Matcher patterns with Slot and Segment

const EMPTY_DICT = ImmutableDict{Symbol, Any}(:____, nothing)


struct RuleRewriteError
    rule
    expr
end

getdepth(::Any) = typemax(Int)

@noinline function Base.showerror(io::IO, err::RuleRewriteError)
    msg = "Failed to apply rule $(err.rule) on expression "
    msg *= sprint(io->showraw(io, err.expr))
    print(io, msg)
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


"""
    @timerewrite expr

If `expr` calls `simplify` or a `RuleSet` object, track the amount of time
it spent on applying each rule and pretty print the timing.

This uses [TimerOutputs.jl](https://github.com/KristofferC/TimerOutputs.jl).

## Example:

```julia

julia> expr = foldr(*, rand([a,b,c,d], 100))
(a ^ 26) * (b ^ 30) * (c ^ 16) * (d ^ 28)

julia> @timerewrite simplify(expr)
 ────────────────────────────────────────────────────────────────────────────────────────────────
                                                         Time                   Allocations
                                                 ──────────────────────   ───────────────────────
                Tot / % measured:                     340ms / 15.3%           92.2MiB / 10.8%

 Section                                 ncalls     time   %tot     avg     alloc   %tot      avg
 ────────────────────────────────────────────────────────────────────────────────────────────────
 ACRule((~y) ^ ~n * ~y => (~y) ^ (~n ...    667   11.1ms  21.3%  16.7μs   2.66MiB  26.8%  4.08KiB
   RHS                                       92    277μs  0.53%  3.01μs   14.4KiB  0.14%     160B
 ACRule((~x) ^ ~n * (~x) ^ ~m => (~x)...    575   7.63ms  14.6%  13.3μs   1.83MiB  18.4%  3.26KiB
 (*)(~(~(x::!issortedₑ))) => sort_arg...    831   6.31ms  12.1%  7.59μs    738KiB  7.26%     910B
   RHS                                      164   3.03ms  5.81%  18.5μs    250KiB  2.46%  1.52KiB
   ...
   ...
 ────────────────────────────────────────────────────────────────────────────────────────────────
(a ^ 26) * (b ^ 30) * (c ^ 16) * (d ^ 28)
```
"""
macro timerewrite(expr)
    :(timerewrite(()->$(esc(expr))))
end

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

# TODO REVIEWME
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
