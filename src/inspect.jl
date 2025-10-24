import AbstractTrees

const inspect_metadata = Ref{Bool}(false)

function AbstractTrees.nodevalue(x::BSImpl.Type)
    T = nameof(MData.variant_type(x))
    str = if !iscall(x)
        string(T, "(", x, ")")
    elseif isadd(x)
        string(T, 
            (variant=string(x.variant),))
    elseif ismul(x)
        string(T,
            (variant=string(x.variant),))
    elseif isdiv(x) || ispow(x)
        string(T)
    else
        string(T,"{", operation(x), "}")
    end

    if inspect_metadata[] && !isnothing(metadata(x))
        str *= string(" metadata=", Tuple(k=>v for (k, v) in metadata(x)))
    end
    Text(str)
end

"""
$(TYPEDSIGNATURES)

Return the children of the symbolic expression `x`, sorted by their order in
the expression.

This function is used internally for printing via AbstractTrees.
"""
function AbstractTrees.children(x::BasicSymbolic)
    iscall(x) ? sorted_arguments(x) : ()
end

"""
    inspect([io::IO=stdout], expr; hint=true, metadata=false)

Inspect an expression tree `expr`. Uses AbstractTrees to print out an expression.

BasicSymbolic expressions will print the Unityper type (ADD, MUL, DIV, POW, SYM, TERM) and the relevant internals as the head, and the children in the subsequent lines as accessed by `arguments`. Other types will get printed as subtrees. Set `metadata=true` to print any metadata carried by the nodes.

Line numbers will be shown, use `pluck(expr, line_number)` to get the sub expression or leafnode starting at line_number.
"""
function inspect end

function inspect(io::IO, x::BasicSymbolic;
        hint=true,
        metadata=inspect_metadata[])

    prev_state = inspect_metadata[]
    inspect_metadata[] = metadata
    lines = readlines(IOBuffer(sprint(io->AbstractTrees.print_tree(io, x))))
    inspect_metadata[] = prev_state
    digits = ceil(Int, log10(length(lines)))
    line_numbers = lpad.(string.(1:length(lines)), digits)
    print(io, join(string.(line_numbers, " ", lines), "\n"))
    hint && print(io, "\n\nHint: call SymbolicUtils.pluck(expr, line_number) to get the subexpression starting at line_number")
end

function inspect(x; hint=true, metadata=inspect_metadata[])
    inspect(stdout, x; hint=hint, metadata=metadata)
end

inspect(io::IO, x; kw...) = println(io, "Not Symbolic: $x")

"""
    pluck(expr, n)

Pluck the `n`th subexpression from `expr` as given by pre-order DFS.
This is the same as the node numbering in `inspect`.
"""
function pluck(x, item)
    collect(Iterators.take(AbstractTrees.PreOrderDFS(x), item))[end]
end
