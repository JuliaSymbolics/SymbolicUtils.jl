using DataStructures

eclass_id(id, T=Real) = term(eclass_id, id, type=T)

const Id = UInt64

struct EGraph
    union::Dict{Id, MutableBinaryMinHeap{Id}} # Equivalent eclass Ids
    equal_classes::Dict{Id, Set} # Id -> eclasses
    hashcons::Dict # Expression -> Id
end

EGraph() = EGraph(Dict(), Dict(), Dict())

function canonical_id(graph, id) # find
    first(graph.union[id])
end

function add(graph, expr) # return Id
    if haskey(graph.hashcons, expr)
        return graph.hashcons[expr]
    else
        id = new_class(graph, expr)
        graph.hascons[expr] = id
    end
end


function merge!(graph, id1, id2)
    cid1 = canonical_id(graph, id1)
    if cid1 == canonical_id(graph, id2)
        cid1
    else
        newset = union!(get!(()->MutableBinaryMinHeap{Id}(), graph.union, id1), 
                       get!(()->MutableBinaryMinHeap{Id}(), graph.union, id2))
        graph.union[id1] = graph.union[id2] = newset
    end
    canonical_id(graph, id1)
end

find(G, a) = first(G.union[a])

function add_recursive(G, expr)
    if istree(expr)
        args = map(x->add_recursive(G,x), unsorted_arguments(expr))
        add(G, Term{symtype(expr)}(operation(expr), args))
    else
        add(G, expr)
    end
end

function canonicalize(graph, term)
    find
    (graph.union, term)
end

function iterate_exprs(graph)
end

function extend_graph(graph, rule)
    rhs = rule.rhs

    try
        # n == 1 means that exactly one term of the input (term,) was matched
        function success(bindings, n)
            if n != 1
                return nothing
            end

            canonical_bindings = EMPTY_IMMUTABLE_DICT
            for (k, val) in bindings
                canonical_bindings = assoc(k, canonicalize(graph, val))
            end
            merge(c, rhs(canonical_bindings))
        end
        c = 
        return rule.matcher(success, (term,), EMPTY_IMMUTABLE_DICT)
    catch err
        throw(RuleRewriteError(rule, term))
    end
end



##### Equality saturation
#

function equality_saturation(expr, rewrites)
    graph = init_egraph(expr)
    for 1=1:100

        matches = []
        for rw in rewrites
            for (c, t) in iterate_exprs(graph)
                rw.matcher((t,), EMPTY_IMMUTABLE_DICT) do bindings, n
                    if n == 1
                        push!(matches, (rw, bindings, c))
                    end
                end
            end
        end

        for (rw, bindings, c)
            c′ = add(graph, rw.rhs(bindings))
            merge!(graph, c, c′)
        end

        rebuild(graph)
end


function init_egraph(expr)
    if istree(expr)
        ...
    end
end
