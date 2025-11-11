# empty Base.ImmutableDict of the correct type
const SymsType = BasicSymbolic{SymReal}
const MatchDict = ImmutableDict{Symbol, SymsType}
const NO_MATCHES = MatchDict() # or {Symbol, Union{Symbol, Real}} ?
const FAIL_DICT = MatchDict(:_fail,0)
const op_map = Dict(:+ => 0, :* => 1, :^ => 1)

"""
data is a symbolic expression, we need to check if respects the rule
rule is a quoted expression, representing part of the rule
matches is the dictionary of the matches found so far

return value is a ImmutableDict
1) if a mismatch is found, FAIL_DICT is returned.
2) if no mismatch is found but no new matches either (for example in mathcing ^2), the original matches is returned
3) otherwise the dictionary of old + new ones is returned that could look like:
Base.ImmutableDict{Symbol, SymbolicUtils.BasicSymbolicImpl.var"typeof(BasicSymbolicImpl)"{SymReal}}(:x => a, :y => b)

TODO matches does assigment or mutation? which is faster?
"""
function check_expr_r(data::SymsType, rule::Expr, matches::MatchDict)
    # println("Checking ",data," against ",rule,", with matches: ",[m for m in matches]...)
    rule.head != :call && error("It happened, rule head is not a call") #it should never happen
    # rule is a slot
    if rule.head == :call && rule.args[1] == :(~)
        if rule.args[2] in keys(matches) # if the slot has already been matched
            # check if it mached the same symbolic expression
            !isequal(matches[rule.args[2]],data) && return FAIL_DICT::MatchDict
            return matches::MatchDict
        else # if never been matched
            # if there is a predicate rule.args[2] is a expression with ::
            if isa(rule.args[2], Expr)
                # check it
                pred = rule.args[2].args[2]
                !eval(pred)(SymbolicUtils.unwrap_const(data)) && return FAIL_DICT
                return Base.ImmutableDict(matches, rule.args[2].args[1], data)::MatchDict
            end
            # if no predicate add match
            return Base.ImmutableDict(matches, rule.args[2], data)::MatchDict
        end
    end
    # if there is a deflsot in the arguments
    p=findfirst(a->isa(a, Expr) && a.args[1] == :~ && isa(a.args[2], Expr) && a.args[2].args[1] == :!,rule.args[2:end])
    if p!==nothing
        # build rule expr without defslot and check it
        if p==1
            newr = Expr(:call, rule.args[1], :(~$(rule.args[2].args[2].args[2])), rule.args[3])
        elseif p==2
            newr = Expr(:call, rule.args[1], rule.args[2], :(~$(rule.args[3].args[2].args[2])))
        else
            error("defslot error")# it should never happen
        end
        rv = check_expr_r(data, newr, matches)
        rv!==FAIL_DICT && return rv::MatchDict
        # if no normal match, check only the non-defslot part of the rule
        rv = check_expr_r(data, rule.args[p==1 ? 3 : 2], matches)
        # if yes match
        rv!==FAIL_DICT && return Base.ImmutableDict(rv, rule.args[p+1].args[2].args[2], get(op_map, rule.args[1], -1))::MatchDict
        return FAIL_DICT::MatchDict
    else
        # rule is a call, check operation and arguments
        # - check operation
        !iscall(data) && return FAIL_DICT::MatchDict
        (Symbol(operation(data)) !== rule.args[1]) && return FAIL_DICT::MatchDict
        # - check arguments
        arg_data = arguments(data); arg_rule = rule.args[2:end];
        (length(arg_data) != length(arg_rule)) && return FAIL_DICT::MatchDict
        if (rule.args[1]===:+) || (rule.args[1]===:*)
            # commutative checks
            for perm_arg_data in permutations(arg_data) # is the same if done on arg_rule right?
                matches_this_perm = ceoaa(perm_arg_data, arg_rule, matches)
                matches_this_perm!==FAIL_DICT && return matches_this_perm::MatchDict
                # else try with next perm
            end
            # if all perm failed
            return FAIL_DICT::MatchDict
        else
            # normal checks
            return ceoaa(arg_data, arg_rule, matches)::MatchDict
        end
    end
end

# check expression of all arguments
function ceoaa(arg_data, arg_rule, matches::MatchDict)
    println(typeof(arg_data), typeof(arg_rule))
    for (a, b) in zip(arg_data, arg_rule)
        matches = check_expr_r(a, b, matches)
        matches===FAIL_DICT && return FAIL_DICT::MatchDict
        # else the match has been added (or not added but confirmed)
    end
    return matches::MatchDict
end

# for when the rule contains a constant, a literal number
function check_expr_r(data::SymsType, rule::Real, matches::MatchDict)
    # println("Checking ",data," against the real ",rule,", with matches: ",[m for m in matches]...)
    unw = unwrap_const(data)
    if isa(unw, Real)
        unw!==rule && return FAIL_DICT::MatchDict
        return matches::MatchDict
    end
    # else always fail
    return FAIL_DICT::MatchDict
end

"""
matches is the dictionary
rhs is the expression to be rewritten into

TODO investigate foo in rhs not working
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
