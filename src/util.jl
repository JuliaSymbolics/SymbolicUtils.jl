# merge two pdicts
function pdict_merge(f, d1::pdict, d2::pdict)
    # Do the least amount of lookups
    length(d1) < length(d2) && return _merge((y,x)->f(x,y), d2,d1)

    acc = d1
    for (k, v) in d2
        if haskey(acc, k)
            acc = assoc(acc, k, f(acc[k], v))
        else
            acc = assoc(acc, k, v)
        end
    end
    acc
end
