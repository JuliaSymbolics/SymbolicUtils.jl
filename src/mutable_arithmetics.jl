import MutableArithmetics as MA

function MA.operate!!(::typeof(+), a::BasicSymbolic, b::BasicSymbolic)
    if SymbolicUtils.isadd(a)
        if SymbolicUtils.isadd(b)
            for (k, v) in b.dict
                a.dict[k] = MA.add!!(get(a.dict, k, 0), v)
            end
        else
            a.dict[b] = MA.add!!(get(a.dict, b, 0), 1)
        end
        return a
    else
        return a + b
    end
end
