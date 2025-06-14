#### Pattern matching
### Matching procedures
# A matcher is a function which takes 3 arguments
# 1. Expression
# 2. Dictionary
# 3. Callback: takes arguments Dictionary × Number of elements matched
#

function matcher(val::Any)
    # if val is a call (like an operation) creates a term matcher or term matcher with defslot
    if iscall(val)
        # if has two arguments and one of them is a DefSlot, create a term matcher with defslot
        # just two arguments bc defslot is only supported with operations with two args: *, ^, +
        if length(arguments(val)) == 2 && any(x -> isa(x, DefSlot), arguments(val))
            return defslot_term_matcher_constructor(val)
        # else return a normal term matcher
        else
            return term_matcher_constructor(val)
        end
    end

    function literal_matcher(next, data, bindings)
        # car data is the first element of data
        islist(data) && isequal(car(data), val) ? next(bindings, 1) : nothing
    end
end

function matcher(slot::Slot)
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
            next(assoc(bindings, slot.name, car(data)), 1)
        end
    end
end

function opposite_sign_matcher(slot::Slot)
    function slot_matcher(next, data, bindings)
        !islist(data) && return nothing
        val = get(bindings, slot.name, nothing)
        if val !== nothing
            if isequal(val, car(data))
                return next(bindings, 1)
            end
        elseif slot.predicate(car(data))
            next(assoc(bindings, slot.name, -car(data)), 1) # this - is the only differenct wrt matcher(slot::Slot)
        end
    end
end

function opposite_sign_matcher(defslot::DefSlot)
    opposite_sign_matcher(Slot(defslot.name, defslot.predicate))
end

# this is called only when defslot_term_matcher finds the operation and tries
# to match it, so no default value used. So the same function as slot_matcher
# can be used
function matcher(defslot::DefSlot)
    matcher(Slot(defslot.name, defslot.predicate))
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

function matcher(segment::Segment)
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

function term_matcher_constructor(term)
    matchers = (matcher(operation(term)), map(matcher, arguments(term))...,)

    function term_matcher(success, data, bindings)
        !islist(data) && return nothing # if data is not a list, return nothing
        !iscall(car(data)) && return nothing # if first element is not a call, return nothing

        function loop(term, bindings′, matchers′) # Get it to compile faster
            if !islist(matchers′)
                if  !islist(term)
                    return success(bindings′, 1)
                end
                return nothing
            end
            car(matchers′)(term, bindings′) do b, n
                loop(drop_n(term, n), b, cdr(matchers′))
            end
            # explenation of above 3 lines:
            # car(matchers′)(b,n -> loop(drop_n(term, n), b, cdr(matchers′)), term, bindings′)
            #                <------ next(b,n) ---------------------------->
            # car = first element of list, cdr = rest of the list, drop_n = drop first n elements of list
            # Calls the first matcher, with the "next" function being loop again but with n terms dropepd from term
            # Term is a linked list (a list and a index). drop n advances the index. when the index sorpasses
            # the length of the list, is considered empty
        end

        result = loop(car(data), bindings, matchers)
        # if data is of the alternative form 1/(...)^(...), it might match with negative exponent
        if operation(term)==^
            alternative_form = (operation(car(data))==/) && arguments(car(data))[1]==1 && iscall(arguments(car(data))[2]) && (operation(arguments(car(data))[2])==^)
            if result === nothing && alternative_form
                denominator = arguments(car(data))[2]
                # let's say data = a^b with a and b can be whatever
                # if b is not a number then call the loop function with a^-b
                if !isa(arguments(denominator)[2], Number)
                    frankestein = arguments(denominator)[1] ^ -(arguments(denominator)[2])
                    result = loop(frankestein, bindings, matchers)
                else
                    # if b is a number, like 3, we cant call loop with a^-3 bc it
                    # will automatically transform into 1/a^3. Therfore we need to
                    # create a matcher that flips the sign of the exponent. I created
                    # this matecher just for `Slot`s and not for terms, because if b
                    # is a number and not a call, certainly doesn't match a term (I hope).
                    if isa(arguments(term)[2], Slot)
                        matchers2 = (matcher(operation(term)), matcher(arguments(term)[1]), opposite_sign_matcher(arguments(term)[2])) # is this ok to be here or should it be outside neg_pow_term_matcher?
                        result = loop(denominator, bindings, matchers2)
                    end
                end
            end
        end
        result
    end
end

# creates a matcher for a term containing a defslot, such as:
# (~x + ...complicated pattern...)     *          ~!y
#    normal part (can bee a tree)   operation     defslot part

# defslot_term_matcher works like this:
# checks wether data is a call.
#     if yes (1): continues like term_matcher (if it finds a match returns (2))
#     if still no match found checks wether data (is just a symbol) or (is a tree not starting with the default operation) 
#          if no returns nothing, rule is not applied
#          if yes (3): adds the pair (default value name, default value) to the found bindings and 
#          calls the success function like term_matcher would do

function defslot_term_matcher_constructor(term)
    a = arguments(term) # lenght two bc defslot term matcher is allowed only with +,* and ^, that accept two arguments
    matchers = (matcher(operation(term)), map(matcher, a)...) # create matchers for the operation and the two arguments of the term
    
    defslot_index = findfirst(x -> isa(x, DefSlot), a) # find the defslot in the term
    defslot = a[defslot_index]
    
    function defslot_term_matcher(success, data, bindings)
        # if data is not a list, return nothing
        !islist(data) && return nothing
        result = nothing
        if iscall(car(data))
            # (1)
            function loop(term, bindings′, matchers′) # Get it to compile faster
                if !islist(matchers′)
                    if  !islist(term)
                        return success(bindings′, 1)
                    end
                    return nothing
                end
                car(matchers′)(term, bindings′) do b, n
                    loop(drop_n(term, n), b, cdr(matchers′))
                end
            end

            result = loop(car(data), bindings, matchers) # Try to eat exactly one term
            # if data is of the alternative form 1/(...)^(...), it might match with negative exponent
            if operation(term)==^
                alternative_form = (operation(car(data))==/) && arguments(car(data))[1]==1 && iscall(arguments(car(data))[2]) && (operation(arguments(car(data))[2])==^)
                if result === nothing && alternative_form
                    denominator = arguments(car(data))[2]
                    # let's say data = a^b with a and b can be whatever
                    # if b is not a number then call the loop function with a^-b
                    if !isa(arguments(denominator)[2], Number)
                        frankestein = arguments(denominator)[1] ^ -(arguments(denominator)[2])
                        result = loop(frankestein, bindings, matchers)
                    else
                        # if b is a number, like 3, we cant call loop with a^-3 bc it
                        # will automatically transform into 1/a^3. Therfore we need to
                        # create a matcher that flips the sign of the exponent. I created
                        # this matecher just for `DefSlot`s and not for terms, because if b
                        # is a number and not a call, certainly doesn't match a term (I hope).
                        if isa(arguments(term)[2], DefSlot)
                            matchers2 = (matcher(operation(term)), matcher(arguments(term)[1]), opposite_sign_matcher(arguments(term)[2])) # is this ok to be here or should it be outside neg_pow_term_matcher?
                            result = loop(denominator, bindings, matchers2)
                        end
                    end
                end
            end
            # (2)
            if result !== nothing
                return result
            end
        end
        
        # if data (is not a tree and is just a symbol) or (is a tree not starting with the default operation)
        if ( !iscall(car(data)) || (iscall(car(data)) && nameof(operation(car(data))) != defslot.operation) )
            other_part_matcher = matchers[defslot_index==2 ? 2 : 3] # find the matcher of the normal part
            
            # checks wether it matches the normal part
            #                             <-----------------(3)------------------------------->
            bindings = other_part_matcher((b,n) -> assoc(b, defslot.name, defslot.defaultValue), data, bindings)
            
            if bindings === nothing
                return nothing
            end
            result = success(bindings, 1)
        end
        result
    end
end
