const onekey = Dict{Union{}, Union{}}()

# something like
#   1//2 * (x^2)(y^3) + 4//5 * x
# is expressed as:
#   Dict(x^2 * y^3 => 1//2, x^1 => 4//5)
# Where x^2 * y^3 is represented as
#   Dict(x=>2, y=>3)
#
function pows_to_term(dict)
    args = [isone(exponent) ? to_symbolic(base) : to_symbolic(base)^exponent
            for (base, exponent) in dict]
    if length(args) == 1
        return args[1]
    else
        return Term(*, args)
    end
end

function lc_to_symbolic(terms)
    args = [isone(coeff) ? pows_to_term(t) : coeff * pows_to_term(t)
             for (t, coeff) in terms if !iszero(coeff)]
    if isempty(args)
        return 0
    elseif length(args) == 1
        return args[1]
    else
        return Term(+, args)
    end
end

quicksimplify(x) = x
function quicksimplify(t::Term)
    op = operation(t)
    if op == (*) || op == (/)
        α, term = mul_term(t)
        return lc_to_symbolic(Dict(term => α))
    elseif op == (+) || op == (-)
        β, comb = pm_term(t)
        dict = iszero(β) ? comb : merge(comb, Dict(onekey=>β))
        return lc_to_symbolic(dict)
    else
        Term{symtype(t)}(operation(t),
                         map(quicksimplify, arguments(t)))
    end
end

function distribute(f, x, tt)
    f.(x,tt)
end

mapvalues(f, d) = Dict(zip(keys(d), f.(values(d))))

function mul_term(t, dict=Dict(); lc=Dict(), distribute=true)
    α = 1
    if t isa AbstractArray
        tt = t
    elseif t isa Term && operation(t) == (/)
        α1, d = mul_term(arguments(t)[1:1], dict)
        α2, d = mul_term(arguments(t)[2:2], Dict())
        merge!(+, dict, mapvalues(-, d))
        return α1/α2, dict
    else
        @assert t isa Term
        tt = arguments(t)
    end

    for a in tt
        if a isa Number
            α *= a
        elseif !(a isa Term)
            dict[a] = get(dict, a, 0) + 1
        elseif a isa Term && operation(a) == (^)
            exponent = get(arguments(a), 2, 1)
            if exponent isa Number
                dict[arguments(a)[1]] = get(dict, arguments(a)[1], 0) + exponent
            else
                dict[a] = get(dict, a, 0) + 1
            end
        elseif operation(a) === (*) || operation(a) === (/)
            # flatten
            α1, _ = mul_term(a, dict; lc=Dict())
            α *= α1
        else
            dict[a] = get(dict, a, 0) + 1
        end
    end
    α, dict
end

function pm_term(tr, dict=Dict{Dict, Number}(); sign=1)
    β = 0
    if tr isa Number
        β += sign*tr
        return β, dict
    elseif !(tr isa Term)
        key = Dict(tr=>1)
        dict[key] = get(dict, key, 0) + sign
        return β, dict
    end
    tt = arguments(tr)

    if operation(tr) === -
        if length(tt) == 2
            β1, _ = pm_term(tt[1], dict, sign=sign)
            β2, _ = pm_term(tt[2], dict, sign=-sign)
            return β1 + β2, dict
        end
    end

    for t in tt
        if t isa Number
            β += sign*t
        elseif !(t isa Term)
            key = Dict(t=>1)
            dict[key] = get(dict, key, 0) + sign
        elseif operation(t) == (^)
            exponent = get(arguments(t), 2, 1)
            if exponent isa Number
                key = Dict(arguments(t)[1]=>exponent)
            else
                key = Dict(t=>1)
            end
            coeff = get(dict, key, 0) + sign
            dict[key] = coeff
        elseif operation(t) === (*) || operation(t) === (/)
            α, inner_term = mul_term(t; lc=dict)

            if iszero(α)
                continue
            else
                coeff = get(dict, inner_term, 0) + sign*α
                dict[inner_term] = coeff
            end
        elseif operation(t) === (+) || operation(t) == (-)
            β1,_ = pm_term(t, dict; sign=sign) # flatten
            β += β1 * sign
        else
            key = Dict(t=>1)
            coeff = get(dict, key, 0) + sign
            dict[key] = coeff
        end
    end

    β, dict
end
