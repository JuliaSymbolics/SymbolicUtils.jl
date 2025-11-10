
# empty Base.ImmutableDict of the correct type
const SymsType = SymbolicUtils.BasicSymbolicImpl.var"typeof(BasicSymbolicImpl)"{SymReal}
const MatchDict = ImmutableDict{Symbol, SymsType}
const NO_MATCHES = MatchDict() # or {Symbol, Union{Symbol, Real}} ?
const FAIL_DICT = MatchDict(:_fail,0)

"""
data is a symbolic expression, we need to check if respects the rule
rule is a quoted expression, representing part of the rule
matches is the dictionary of the matches found so far

return value is a ImmutableDict
1) if a mismatch is found, FAIL_DICT is returned.
2) if no mismatch is found but no new matches either (for example in mathcing ^2), the original matches is returned
3) otherwise the dictionary of old + new ones is returned that could look like:
Base.ImmutableDict{Symbol, SymbolicUtils.BasicSymbolicImpl.var"typeof(BasicSymbolicImpl)"{SymReal}}(:x => a, :y => b)
"""
# TODO matches does assigment or mutation? which is faster?
function check_expr_r(data::SymsType, rule::Expr, matches::MatchDict)::MatchDict
    # print("Checking "); show(data); print(" rule "); show(rule); println()
    rule.head != :call && error("It happened") #it should never happen
    # rule is a slot or defslot
    if rule.head == :call && rule.args[1] == :(~)
        if rule.args[2] in keys(matches) # if the slot has already been matched
            # check if it mached the same symbolic expression
            !isequal(matches[rule.args[2]],data) && return FAIL_DICT
            return matches
        else # if never been matched
            # if there is a predicate
            if isa(rule.args[2], Expr)
                rule.args[2].head != :(::) && error("it happened") # it should never happen
                # check it
                pred = rule.args[2].args[2]
                !eval(pred)(SymbolicUtils.unwrap_const(data)) && return FAIL_DICT
                return Base.ImmutableDict(matches, rule.args[2].args[1], data)
            end
            # if no predicate add match
            return Base.ImmutableDict(matches, rule.args[2], data)
        end
    end
    # rule is a call, check operation and arguments
    # - check operation
    !iscall(data) && return FAIL_DICT
    (Symbol(operation(data)) !== rule.args[1]) && return FAIL_DICT
    # - check arguments
    arg_data = arguments(data); arg_rule = rule.args[2:end];
    (length(arg_data) != length(arg_rule)) && return FAIL_DICT
    for (a, b) in zip(arg_data, arg_rule)
        new_matches = check_expr_r(a, b, matches)
        if new_matches===FAIL_DICT
            return FAIL_DICT
        end
        # else the match has been added (or confirmed)
        matches = new_matches
    end
    return matches
end

# for when the rule contains a constant, a literal number
function check_expr_r(data::SymsType, rule::Real, matches::MatchDict)::MatchDict
    # print("Checking "); show(data); print(" against the real "); show(rule); println()
    unw = unwrap_const(data)
    if isa(unw, Real)
        if unw!==rule
            return FAIL_DICT
        end
        return matches
    end
    # else always fail
    return FAIL_DICT
end

"""

"""
function rewrite(matches::MatchDict, rhs::Expr)::SymsType
    if rhs.head != :call
        error("It happened") #it should never happen
    end
    # rhs is a slot or defslot
    if rhs.head == :call && rhs.args[1] == :(~)
        var_name = rhs.args[2]
        if haskey(matches, var_name)
            return matches[var_name]
        else
            error("No match found for variable $(var_name)") #it should never happen
        end
    end
    # rhs is a call, reconstruct it
    op = eval(rhs.args[1])
    args = SymsType[]
    for a in rhs.args[2:end]
        push!(args, rewrite(matches, a))
    end
    return op(args...)
end

function rewrite(matches::MatchDict, rhs::Real)::SymsType
    return rhs
end

function rule2(rule::Pair{Expr, Expr}, exp::SymsType)::Union{SymsType, Nothing}
    m = check_expr_r(exp, rule.first, NO_MATCHES)
    m===FAIL_DICT && return nothing
    return rewrite(m, rule.second)
end
