# A matcher is a closure that takes a success, data, bindings
function ematch(l, r, expr)
    matches = instantiate(l, expr)
    c = get_class(substitute(l, matches))
    if !isnothing(matches)
        merge_into_class(c, substitute(r, matches))
    end
    return c
end
