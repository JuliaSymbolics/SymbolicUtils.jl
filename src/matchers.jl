#### Pattern matching
### Matching procedures
# A matcher is a function which takes 3 arguments
# 1. Expression
# 2. Dictionary
# 3. Callback: takes arguments Dictionary × Number of elements matched
#

function matcher(val::Any, acSets)
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
function matcher(slot::Slot, acSets)
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
function matcher(defslot::DefSlot, acSets)
    matcher(Slot(defslot.name, defslot.predicate), nothing) # slot matcher doesnt use acsets
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

function term_matcher_constructor(term, acSets)
    matchers = (matcher(operation(term), acSets), map(x->matcher(x,acSets), arguments(term))...,)
    
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
    if operation(term) === ^
        function pow_term_matcher(success, data, bindings)
            !islist(data) && return nothing # if data is not a list, return nothing
            data = car(data) # from (..., ) to ...
            !iscall(data) && return nothing # if first element is not a call, return nothing
            
            result = loop(data, bindings, matchers)
            result !== nothing && return success(result, 1)
            
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
                result !== nothing && return success(result, 1)
            end

            return nothing
        end
        return pow_term_matcher
    # if we want to do commutative checks, i.e. call matcher with different order of the arguments
    elseif acSets!==nothing && operation(term) in [+, *]
        cond = false
        if operation(term)==*
            for a in arguments(term)
                if iscall(a) && operation(a)===^
                    cond = true
                end
            end
        end

        function commutative_term_matcher(success, data, bindings)
            !islist(data) && return nothing # if data is not a list, return nothing
            data = car(data)
            !iscall(data) && return nothing # if first element is not a call, return nothing
            if cond && (operation(data)===/)
                nnmrt = arguments(data)[1]
                den = arguments(data)[2]
                if iscall(den) && operation(den)===^
                    new_den = Term{symtype(nnmrt)}(^,[arguments(den)[1], -1*arguments(den)[2]])
                elseif iscall(den) && operation(den)===sqrt
                    new_den = Term{symtype(nnmrt)}(^,[arguments(den)[1], -1//2])
                elseif iscall(den) && operation(den)===*
                    new_den=[]
                    for a in arguments(den)
                        if iscall(a) && operation(a)===^
                            push!(new_den, Term{symtype(nnmrt)}(^,[arguments(a)[1], -1*arguments(a)[2]]))
                        elseif iscall(a) && operation(a)===sqrt
                            push!(new_den, Term{symtype(nnmrt)}(^,[arguments(a)[1], -1//2]))
                        else
                            push!(new_den, Term{symtype(nnmrt)}(^,[a, -1]))
                        end
                    end
                    new_den = *(new_den...)
                else
                    new_den = Term{symtype(nnmrt)}(^,[den, -1])
                end
                if length(nnmrt) == 1
                    data = *(new_den, nnmrt)
                else
                    data = *(new_den, nnmrt...)
                end
                println("frankestein data: $data")
            elseif operation(term) !== operation(data)
                return nothing # if the operation of data is not the correct one, don't even try
            end
            
            T = symtype(data)
            if T <: Number
                f = operation(data)
                data_args = arguments(data)
                
                for inds in acSets(eachindex(data_args), length(data_args))
                    candidate = Term{T}(f, @views data_args[inds])

                    result = loop(candidate, bindings, matchers)
                    result !== nothing && return success(result,1)
                end
            # if data does not subtype to number, it might not be commutative
            else
                # call the normal matcher
                result = loop(data, bindings, matchers)
                result !== nothing && return success(result, 1)
            end
            return nothing
        end
        return commutative_term_matcher
    # if the operation is sqrt, we have to match also ^(1//2)
    elseif operation(term)==sqrt
        function sqrt_matcher(success, data, bindings)
            !islist(data) && return nothing # if data is not a list, return nothing
            data = car(data)
            !iscall(data) && return nothing # if first element is not a call, return nothing
            
            # do the normal matcher
            result = loop(data, bindings, matchers)
            result !== nothing && return success(result, 1)

            if (operation(data) === ^) && (arguments(data)[2] === 1//2)
                T = symtype(arguments(data)[1])
                frankestein = Term{T}(sqrt,[arguments(data)[1]])
                result = loop(frankestein, bindings, matchers)
                result !== nothing && return success(result, 1)
            end
            return nothing
        end
        return sqrt_matcher
    # if the operation is exp, we have to match also ℯ^
    elseif operation(term)==exp
        function exp_matcher(success, data, bindings)
            !islist(data) && return nothing # if data is not a list, return nothing
            data = car(data)
            !iscall(data) && return nothing # if first element is not a call, return nothing
            
            # do the normal matcher
            result = loop(data, bindings, matchers)
            result !== nothing && return success(result, 1)

            if (operation(data) === ^) && (arguments(data)[1] === ℯ)
                T = symtype(arguments(data)[2])
                frankestein = Term{T}(exp,[arguments(data)[2]])
                result = loop(frankestein, bindings, matchers)
                result !== nothing && return success(result, 1)
            end
            return nothing
        end
        return exp_matcher
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

# Note: there is a bit of a waste here bc the matcher get created twice, both 
# in the normal_matcher and in defslot_matcher and other_part_matcher
function defslot_term_matcher_constructor(term, acSets)
    a = arguments(term)
    defslot_index = findfirst(x -> isa(x, DefSlot), a) # find the defslot in the term
    defslot = a[defslot_index]
    defslot_matcher = matcher(defslot, acSets)
    if length(a) == 2
        other_part_matcher = matcher(a[defslot_index == 1 ? 2 : 1], acSets)
    else
        # if we hare here the operation is a multiplication or sum of n>2 terms
        # (because ^ cannot have more than 2 terms).
        # creates the term matcher of the multiplication or sum of n-1 terms
        others = [a[i] for i in eachindex(a) if i != defslot_index]
        T = symtype(term)
        f = operation(term)
        other_part_matcher = term_matcher_constructor(Term{T}(f, others), acSets)
    end
    
    normal_matcher = term_matcher_constructor(term, acSets)

    function defslot_term_matcher(success, data, bindings)
        !islist(data) && return nothing # if data is not a list, return nothing
        # call the normal matcher, with success function that returns the bindings (foo1)
        #                       <-foo1->
        result = normal_matcher((b,n)->b, data, bindings)
        result !== nothing && return success(result, 1)
        # if no match, try to match with a defslot.
        # checks whether it matches the normal part if yes executes foo2
        # foo2: adds the pair (default value name, default value) to the found bindings
        #       after checking predicate and presence in the bindings. If added 
        #       successfully returns the bindings (foo3), otherwise return nothing
        #                           <-------------------foo2----------------------------------->
        #                                                  <-foo3->
        result = other_part_matcher((b,n)->defslot_matcher((b,n)->b, (defslot.defaultValue,), b), data, bindings)
        result !== nothing && return success(result, 1)
        nothing
    end
end
