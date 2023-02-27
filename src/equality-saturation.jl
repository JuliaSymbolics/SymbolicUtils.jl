function ematch(rule, expr)
    matches = instantiate(l, expr)
    c = get_class(substitute(l, matches))
    if !isnothing(matches)
        merge_into_class(c, substitute(r, matches))
    end
    return c
end
