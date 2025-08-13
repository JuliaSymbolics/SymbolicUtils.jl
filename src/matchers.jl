#### Pattern matching
### Matching procedures
# A matcher is a function which takes 3 arguments
# 1. Expression
# 2. Dictionary
# 3. Callback: takes arguments Dictionary × Number of elements matched
#

function matcher(val::Any, acSets, condition)
    # if val is a call (like an operation) creates a term matcher or term matcher with defslot
    if iscall(val)
        # if has two arguments and one of them is a DefSlot, create a term matcher with defslot
        # just two arguments bc defslot is only supported with operations with two args: *, ^, +
        if any(x -> isa(x, DefSlot), arguments(val))
            return defslot_term_matcher_constructor(val, acSets, condition)
        end
        # else return a normal term matcher
        return term_matcher_constructor(val, acSets, condition)
    end

    function literal_matcher(next, data, bindings)
        # car data is the first element of data
        islist(data) && isequal(car(data), val) ? next(bindings, 1) : nothing
    end
end

# acSets and condition are not used but needs to be there in case 
# matcher(::Slot) is directly called from the macro
function matcher(slot::Slot, acSets, condition)
    function slot_matcher(next, data, bindings)
        !islist(data) && return nothing
        val = get(bindings, slot.name, nothing)
        # if slot name already is in bindings, check if it matches
        if val !== nothing
            if isequal(val, car(data))
                return next(bindings, 1)
            end
        # elseif the first element of data matches the slot predicate, add it to bindings and call next
        elseif slot.predicate(car(data))
            # println("slot of $slot matched")
            next(assoc(bindings, slot.name, car(data)), 1)
        end
    end
end

# this is called only when defslot_term_matcher finds the operation and tries
# to match it, so no default value used. So the same function as slot_matcher
# can be used
function matcher(defslot::DefSlot, acSets, condition)
    matcher(Slot(defslot.name, defslot.predicate), nothing, nothing)
end

# returns n == offset, 0 if failed
function trymatchexpr(data, value, n)
    if !islist(value)
        return n
    elseif islist(value) && islist(data)
        if !islist(data)
            # didn't fully match
            return nothing
        end

        while isequal(car(value), car(data))
            n += 1
            value = cdr(value)
            data = cdr(data)

            if !islist(value)
                return n
            elseif !islist(data)
                return nothing
            end
        end

        return !islist(value) ? n : nothing
    elseif isequal(value, data)
        return n + 1
    end
end

function matcher(segment::Segment, acSets)
    function segment_matcher(success, data, bindings)
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

                !segment.predicate(subexpr) && continue
                res = success(assoc(bindings, segment.name, subexpr), i)
                res !== nothing && break
            end

            return res
        end
    end
end

function term_matcher_constructor(term, acSets, condition)
    matchers = (
        matcher(operation(term), acSets, condition),
        map(x->matcher(x,acSets, condition), arguments(term))...,
    )
    
    function loop(term, bindings′, matchers′) # Get it to compile faster
        if !islist(matchers′)
            if  !islist(term)
                return bindings′
            end
            return nothing
        end
        car(matchers′)(term, bindings′) do b, n
            loop(drop_n(term, n), b, cdr(matchers′))
        end
        # explanation of above 3 lines:
        # car(matchers′)(b,n -> loop(drop_n(term, n), b, cdr(matchers′)), term, bindings′)
        #                <------ next(b,n) ---------------------------->
        # car = first element of list, cdr = rest of the list, drop_n = drop first n elements of list
        # Calls the first matcher, with the "next" function being loop again but with n terms dropepd from term
        # Term is a linked list (a list and a index). drop n advances the index. when the index sorpasses
        # the length of the list, is considered empty
    end

    # if condition errors, this means not all the bindings 
    # are associated, so we are not at the end of the match. So
    # we continue to the next matchers
    function check_conditions(result)
        result === nothing && return false
        try
            tmp = condition(result)
            # tmp==nothing means no conditions are present
            tmp===nothing && return true
            return tmp
        catch e
            # println("condition failed, continuing")
            return true
        end
    end

    # if the operation is a pow, we have to match also 1/(...)^(...) with negative exponent
    if operation(term) === ^
        function pow_term_matcher(success, data, bindings)
            # println("in ^ matcher of $term with data $data")
            !islist(data) && return nothing # if data is not a list, return nothing
            data = car(data) # from (..., ) to ...
            !iscall(data) && return nothing # if first element is not a call, return nothing
            
            result = loop(data, bindings, matchers)
            check_conditions(result) && return success(result, 1)
            
            frankestein = nothing
            if (operation(data) === ^) && iscall(arguments(data)[1]) && (operation(arguments(data)[1]) === /) && isequal(arguments(arguments(data)[1])[1], 1)
                # if data is of the alternative form (1/...)^(...)
                one_over_smth = arguments(data)[1]
                T = symtype(one_over_smth)
                frankestein = Term{T}(^, [arguments(one_over_smth)[2], -arguments(data)[2]])
            elseif (operation(data) === /) && isequal(arguments(data)[1], 1) && iscall(arguments(data)[2]) && (operation(arguments(data)[2]) === ^)
                # if data is of the alternative form 1/(...)^(...)
                denominator = arguments(data)[2]
                T = symtype(denominator)
                frankestein = Term{T}(^, [arguments(denominator)[1], -arguments(denominator)[2]])
            elseif (operation(data) === /) && isequal(arguments(data)[1], 1)
                # if data is of the alternative form 1/(...), it might match with exponent = -1
                denominator = arguments(data)[2]
                T = symtype(denominator)
                frankestein = Term{T}(^, [denominator, -1])
            elseif operation(data)===exp
                # if data is a exp call, it might match with base e
                T = symtype(arguments(data)[1])
                frankestein = Term{T}(^,[ℯ, arguments(data)[1]])
            elseif operation(data)===sqrt
                # if data is a sqrt call, it might match with exponent 1//2
                T = symtype(arguments(data)[1])
                frankestein = Term{T}(^,[arguments(data)[1], 1//2])
            end

            if frankestein !==nothing
                result = loop(frankestein, bindings, matchers)
                check_conditions(result) && return success(result, 1)
            end

            return nothing
        end
        return pow_term_matcher
    # if we want to do commutative checks, i.e. call matcher with different order of the arguments
    elseif acSets!==nothing && operation(term) in [+, *]
        function commutative_term_matcher(success, data, bindings)
            # println("in +* matcher of $term with data $data")
            !islist(data) && return nothing # if data is not a list, return nothing
            !iscall(car(data)) && return nothing # if first element is not a call, return nothing
            operation(term) !== operation(car(data)) && return nothing # if the operation of data is not the correct one, don't even try
            
            T = symtype(car(data))
            if T <: Number
                f = operation(car(data))
                data_args = arguments(car(data))
                
                for inds in acSets(eachindex(data_args), length(data_args))
                    candidate = Term{T}(f, @views data_args[inds])

                    result = loop(candidate, bindings, matchers)                
                    check_conditions(result) && return success(result, 1)
                end
            # if car(data) does not subtype to number, it might not be commutative
            else
                # call the normal matcher
                result = loop(car(data), bindings, matchers)
                check_conditions(result) && return success(result, 1)
            end
            return nothing
        end
        return commutative_term_matcher
    else
        function term_matcher(success, data, bindings)
            !islist(data) && return nothing # if data is not a list, return nothing
            !iscall(car(data)) && return nothing # if first element is not a call, return nothing
            
            result = loop(car(data), bindings, matchers)
            check_conditions(result) && return success(result, 1)
            return nothing
        end
        return term_matcher
    end
end

# creates a matcher for a term containing a defslot, such as:
# (~x + ...complicated pattern...)     *          ~!y
#    normal part (can bee a tree)   operation     defslot part
function defslot_term_matcher_constructor(term, acSets, condition)
    a = arguments(term)
    defslot_index = findfirst(x -> isa(x, DefSlot), a) # find the defslot in the term
    defslot = a[defslot_index]
    if length(a) == 2
        other_part_matcher = matcher(a[defslot_index == 1 ? 2 : 1], acSets, condition)
    else
        others = [a[i] for i in eachindex(a) if i != defslot_index]
        T = symtype(term)
        f = operation(term)
        other_part_matcher = term_matcher_constructor(Term{T}(f, others), acSets, condition)
    end
    
    normal_matcher = term_matcher_constructor(term, acSets, condition)



    function defslot_term_matcher(success, data, bindings)
        # println("in defslotmatcher of $term with data $data")
        !islist(data) && return nothing # if data is not a list, return nothing
        # call the normal matcher, with success function foo1 that simply returns the bindings
        #                       <--foo1-->
        result = normal_matcher((b,n) -> b, data, bindings)
        result !== nothing && return success(result, 1)
        # println("no match, trying defslot")
        # if no match, try to match with a defslot.
        # checks whether it matches the normal part if yes executes foo2
        # foo2: adds the pair (default value name, default value) to the found bindings
        #                           <-------------------foo2---------------------------->
        result = other_part_matcher((b,n) -> assoc(b, defslot.name, defslot.defaultValue), data, bindings)
        result === nothing && return nothing
        # println("defslot match!")
        try
            tmp = condition(result)
            # tmp==nothing means no conditions are present
            if tmp===nothing || tmp
                return success(result, 1)
            end
        catch e
            # println("condition failed, continuing")
            return success(result, 1)
        end
    end
end