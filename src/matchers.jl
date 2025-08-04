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
        args = parent(arguments(val))
        if length(args) == 2 && any(x -> isa(x, DefSlot), args)
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
            rest = car(data)
            binds = assoc(bindings, slot.name, rest)
            next(binds, 1)
        end
    end
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
            # explanation of above 3 lines:
            # car(matchers′)(b,n -> loop(drop_n(term, n), b, cdr(matchers′)), term, bindings′)
            #                <------ next(b,n) ---------------------------->
            # car = first element of list, cdr = rest of the list, drop_n = drop first n elements of list
            # Calls the first matcher, with the "next" function being loop again but with n terms dropepd from term
            # Term is a linked list (a list and a index). drop n advances the index. when the index sorpasses
            # the length of the list, is considered empty
        end

        loop(car(data), bindings, matchers) # Try to eat exactly one term
    end
end

# creates a matcher for a term containing a defslot, such as:
# (~x + ...complicated pattern...)     *          ~!y
#    normal part (can bee a tree)   operation     defslot part

# defslot_term_matcher works like this:
# checks whether data starts with the default operation.
#     if yes (1): continues like term_matcher
#     if no checks whether data matches the normal part
#          if no returns nothing, rule is not applied
#          if yes (2): adds the pair (default value name, default value) to the found bindings and 
#          calls the success function like term_matcher would do

function defslot_term_matcher_constructor(term)
    a = arguments(term) # length two bc defslot term matcher is allowed only with +,* and ^, that accept two arguments
    matchers = (matcher(operation(term)), map(matcher, a)...) # create matchers for the operation and the two arguments of the term
    
    defslot_index = findfirst(x -> isa(x, DefSlot), a) # find the defslot in the term
    defslot = a[defslot_index]
    
    function defslot_term_matcher(success, data, bindings)
        # if data is not a list, return nothing
        !islist(data) && return nothing
        # if data (is not a tree and is just a symbol) or (is a tree not starting with the default operation)
        if !iscall(car(data)) || (iscall(car(data)) && nameof(operation(car(data))) != defslot.operation)
            other_part_matcher = matchers[defslot_index==2 ? 2 : 3] # find the matcher of the normal part
            
            # checks whether it matches the normal part
            #                             <-----------------(2)------------------------------->
            bindings = other_part_matcher((b,n) -> assoc(b, defslot.name, defslot.defaultValue), data, bindings)
            
            if bindings === nothing
                return nothing
            end
            return success(bindings, 1)
        end

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

        loop(car(data), bindings, matchers) # Try to eat exactly one term
    end
end
