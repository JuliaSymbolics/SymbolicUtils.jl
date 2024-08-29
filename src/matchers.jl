#### Pattern matching
### Matching procedures
# A matcher is a function which takes 3 arguments
# 1. Expression
# 2. Dictionary
# 3. Callback: takes arguments Dictionary × Number of elements matched
#
function matcher(val::Any)
    matcher(val, false)
end

# `fullac_flag == true` enables fully nested associative-commutative pattern matching
function matcher(val::Any, fullac_flag)
    iscall(val) && return term_matcher(val, fullac_flag)
    function literal_matcher(next, data, bindings)
        islist(data) && isequal(car(data), val) ? next(bindings, 1) : nothing
    end
end

function matcher(slot::Slot, fullac_flag) # fullac_flag unused but needed to keep the interface uniform
    function slot_matcher(next, data, bindings)
        !islist(data) && return
        val = get(bindings, slot.name, nothing)
        if val !== nothing
            if isequal(val, car(data))
                return next(bindings, 1)
            end
        else
            if slot.predicate(car(data))
                next(assoc(bindings, slot.name, car(data)), 1)
            end
        end
    end
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

function matcher(segment::Segment, fullac_flag) # fullac_flag unused but needed to keep the interface uniform
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

function term_matcher(term, fullac_flag = false)
    matchers = (matcher(operation(term), fullac_flag), map(a -> matcher(a, fullac_flag), arguments(term))...,)
    function term_matcher(success, data, bindings)

        !islist(data) && return nothing
        !iscall(car(data)) && return nothing

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

        if !(fullac_flag && iscall(term) && operation(term) in ((+), (*)))
            loop(car(data), bindings, matchers) # Try to eat exactly one term
        else # try all permutations of `car(data)` to see if a match is possible
            data1 = car(data)
            args = arguments(data1)
            op = operation(data1)
            data_arg_perms = permutations(args)
            result = nothing
            T = symtype(data)
            if op != operation(term)
                return nothing
            end
            for perm in data_arg_perms
                data_permuted = Term{T}(op, perm)
                result = loop(data_permuted, bindings, matchers) # Try to eat exactly one term
                if !(result isa Nothing)
                    break
                end
            end
            return result
        end
    end
end
