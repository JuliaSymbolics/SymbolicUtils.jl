#### Pattern matching
### Matching procedures
# A matcher is a function which takes 3 arguments
# 1. Expression
# 2. Dictionary
# 3. Callback: takes arguments Dictionary × Number of elements matched
#

function matcher(val::Any; acSets = nothing)
    # if val is a call (like an operation) creates a term matcher or term matcher with defslot
    if iscall(val)
        # if has two arguments and one of them is a DefSlot, create a term matcher with defslot
        # just two arguments bc defslot is only supported with operations with two args: *, ^, +
        if any(x -> isa(x, DefSlot), arguments(val))
            return defslot_term_matcher_constructor(val, acSets)
        end
        # else return a normal term matcher
        return term_matcher_constructor(val, acSets)
    end

    function literal_matcher(next, data, bindings)
        # car data is the first element of data
        islist(data) && isequal(car(data), val) ? next(bindings, 1) : nothing
    end
end

# acSets is not used but needs to be there in case matcher(::Slot) is directly called from the macro
function matcher(slot::Slot; acSets = nothing)
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

# this is called only when defslot_term_matcher finds the operation and tries
# to match it, so no default value used. So the same function as slot_matcher
# can be used
function matcher(defslot::DefSlot; acSets = nothing)
    matcher(Slot(defslot.name, defslot.predicate))
end

# function opposite_sign_matcher(val::Any)
# end

function opposite_sign_matcher(slot::Slot)
    function slot_matcher(next, data, bindings)
        !islist(data) && return nothing
        val = get(bindings, slot.name, nothing)
        if val !== nothing
            if isequal(val, car(data))
                return next(bindings, 1)
            end
        elseif slot.predicate(car(data))
            next(assoc(bindings, slot.name, -car(data)), 1) # this - is the only difference wrt matcher(slot::Slot)
        end
    end
end

function opposite_sign_matcher(defslot::DefSlot)
    opposite_sign_matcher(Slot(defslot.name, defslot.predicate))
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

function matcher(segment::Segment; acSets=nothing)
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

function term_matcher_constructor(term, acSets)
    matchers = (matcher(operation(term); acSets=acSets), map(x->matcher(x;acSets=acSets), arguments(term))...,)
    
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

    # if the operation is a pow, we have to match also 1/(...)^(...) with negative exponent
    if operation(term)==^
        # the below 4 lines could stay in the function term_matcher_pow, but 
        # are here to speed up the rule matcher function
        cond = isa(arguments(term)[2], Slot) || isa(arguments(term)[2], DefSlot)
        if cond
            matchers_modified = (matcher(operation(term)), matcher(arguments(term)[1]), opposite_sign_matcher(arguments(term)[2])) # is this ok to be here or should it be outside neg_pow_term_matcher?
        end
        
        function term_matcher_pow(success, data, bindings)
            !islist(data) && return nothing # if data is not a list, return nothing
            !iscall(car(data)) && return nothing # if first element is not a call, return nothing
            
            result = loop(car(data), bindings, matchers)
            result !== nothing && return success(result, 1)
            
            # if data is of the alternative form 1/(...)^(...), it might match with negative exponent
            if (operation(car(data))==/) && arguments(car(data))[1]==1 && iscall(arguments(car(data))[2]) && (operation(arguments(car(data))[2])==^)
                denominator = arguments(car(data))[2]
                # let's say data = a^b with a and b can be whatever
                # if b is not a number then call the loop function with a^-b
                if !isa(arguments(denominator)[2], Number)
                    frankestein = arguments(denominator)[1] ^ -(arguments(denominator)[2])
                    result = loop(frankestein, bindings, matchers)
                # if b is a number, like 3, we cant call loop with a^-3 bc it
                # will automatically transform into 1/a^3. Therefore we need to
                # create a matcher that flips the sign of the exponent. I created
                # this matecher just for `Slot`s and `DefSlot`s, but not for 
                # terms or literals,  because if b is a number and not a call,
                # certainly doesn't match a term (I hope).
                # Also not a literal because...?
                elseif cond
                    result = loop(denominator, bindings, matchers_modified)
                end
            end
            result !== nothing && return success(result, 1)
            return nothing
        end
        return term_matcher_pow
    # if the operation is commutative
    elseif acSets!==nothing && !isa(arguments(term)[1], Segment) && operation(term) in [+, *]
        function term_matcher_comm(success, data, bindings)
            !islist(data) && return nothing # if data is not a list, return nothing
            !iscall(car(data)) && return nothing # if first element is not a call, return nothing
            
            T = symtype(car(data))
            f = operation(car(data))
            data_args = arguments(car(data))

            for inds in acSets(eachindex(data_args), length(arguments(term)))
                candidate = Term{T}(f, @views data_args[inds])

                result = loop(candidate, bindings, matchers)                
                result !== nothing && length(data_args) == length(inds) && return success(result,1)
            end
            return nothing
        end
        return term_matcher_comm
    else
        function term_matcher(success, data, bindings)
            !islist(data) && return nothing # if data is not a list, return nothing
            !iscall(car(data)) && return nothing # if first element is not a call, return nothing
            
            result = loop(car(data), bindings, matchers)
            result !== nothing && return success(result, 1)
            return nothing
        end
        return term_matcher
    end
end

# creates a matcher for a term containing a defslot, such as:
# (~x + ...complicated pattern...)     *          ~!y
#    normal part (can bee a tree)   operation     defslot part
function defslot_term_matcher_constructor(term, acSets)
    a = arguments(term)
    defslot_index = findfirst(x -> isa(x, DefSlot), a) # find the defslot in the term
    defslot = a[defslot_index]
    if length(a) == 2
        other_part_matcher = matcher(a[defslot_index == 1 ? 2 : 1]; acSets = acSets)
    else
        others = [a[i] for i in eachindex(a) if i != defslot_index]
        T = symtype(term)
        f = operation(term)
        other_part_matcher = term_matcher_constructor(Term{T}(f, others), acSets)
    end
    
    normal_matcher = term_matcher_constructor(term, acSets)

    function defslot_term_matcher(success, data, bindings)
        !islist(data) && return nothing # if data is not a list, return nothing
        result = normal_matcher(success, data, bindings)
        result !== nothing && return result
        # if no match, try to match with a defslot.
        # checks whether it matches the normal part if yes executes (foo)
        # (foo): adds the pair (default value name, default value) to the found bindings
        #                           <------------------(foo)---------------------------->
        result = other_part_matcher((b,n) -> assoc(b, defslot.name, defslot.defaultValue), data, bindings)
        result !== nothing && return success(result, 1)
        nothing
    end
end
