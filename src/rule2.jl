
# function create_n_expressions(n::Int)::Nothing
#     @syms x
#     exps = SymbolicUtils.BasicSymbolicImpl.var"typeof(BasicSymbolicImpl)"{SymReal}[]
#     for i in 1:n
#         e = :(∫(((~f) + (~!g)*(~x))^(~!q)*((~!a) + (~!b)*log((~!c)*((~d) + (~!e)*(~x))^(~!n)))^(~!p),(~x)) =>
#         1⨸(~e)*int_and_subst(((~f)*(~x)⨸(~d))^(~q)*((~a) + (~b)*log((~c)*(~x)^(~n)))^(~p),  (~x), (~x), (~d) + (~e)*(~x), "3_3_2"))
#         push!(exps, e)
#     end
# end
# 
# function create_n_rules(n::Int)::Nothing
#     @syms x ∫(var1, var2)
#     rules = Rule[]
#     for i in 1:n
#         r = @rule ∫(((~f) + (~!g)*(~x))^(~!q)*((~!a) + (~!b)*log((~!c)*((~d) + (~!e)*(~x))^(~!n)))^(~!p),(~x)) =>
#         1⨸(~e)*int_and_subst(((~f)*(~x)⨸(~d))^(~q)*((~a) + (~b)*log((~c)*(~x)^(~n)))^(~p),  (~x), (~x), (~d) + (~e)*(~x), "3_3_2")
#         push!(rules, r)
#     end
# end

# empty base imuttable dict of the correct type

const SymsType = SymbolicUtils.BasicSymbolicImpl.var"typeof(BasicSymbolicImpl)"{SymReal}
const MatchDict = ImmutableDict{Symbol, SymsType}
const NO_MATCHES = MatchDict() # or {Symbol, Union{Symbol, Real}} ?
const FAIL_DICT = MatchDict(:_fail,0)

function merge_immutable_dicts(d1::MatchDict, d2::MatchDict)::MatchDict
    result = d1
    for (k, v) in d2
        result = Base.ImmutableDict(result, k, v)
    end
    return result
end

@syms ∫(var1, var2) 
"""
against is a quoted expression
to_check is a symbolic expression

return value is the dictionary containing the bindings matches found.
1) if a mismatch is found, FAIL_DICT is returned.
2) if no mismatch is found but no matches either (for example in mathcing ^2), a NO_MATCHES is returned.
3) otherwise the dictionary of matches is returned that could look like:
Base.ImmutableDict{Symbol, SymbolicUtils.BasicSymbolicImpl.var"typeof(BasicSymbolicImpl)"{SymReal}}(:x => a, :y => b)

"""
function check_expr_r(to_check::SymsType, against::Expr)::MatchDict
    # print("Checking "); show(to_check); print(" against "); show(against); println()
    if against.head != :call
        error("It happened") #it should never happen
    end
    # against is a slot or defslot
    if against.head == :call && against.args[1] == :(~)
        # TODO add predicates
        return MatchDict(against.args[2], to_check)
    end
    # against is a call, check operation and arguments
    !iscall(to_check) && return FAIL_DICT
    # check operation
    (operation(to_check) !== eval(against.args[1])) && return FAIL_DICT
    # check arguments
    arg_to_check = arguments(to_check)
    arg_against = against.args[2:end]
    (length(arg_to_check) != length(arg_against)) && return FAIL_DICT

    bind_args = NO_MATCHES
    for (a, b) in zip(arg_to_check, arg_against)
        bind_arg = check_expr_r(a, b)
        if bind_arg===FAIL_DICT
            return FAIL_DICT
        elseif bind_arg!==NO_MATCHES
            bind_args = merge_immutable_dicts(bind_args, bind_arg)
        end
        # if bind_arg===NO_MATCHES continue to next
    end
    return bind_args
end

function check_expr_r(to_check::SymsType, against::Real)::MatchDict
    # print("Checking "); show(to_check); print(" against the real "); show(against); println()
    unw = unwrap_const(to_check)
    # if we have literal numbers in the rule
    if isa(unw, Real)
        if unw!==against
            return FAIL_DICT
        end
        return NO_MATCHES
    end
    # else always match
    return MatchDict(to_check, against)
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
    m = check_expr_r(exp, rule.first)
    m===FAIL_DICT && return nothing
    return rewrite(m, rule.second)
end
