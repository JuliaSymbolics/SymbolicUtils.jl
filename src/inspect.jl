import AbstractTrees

function AbstractTrees.nodevalue(x::Symbolic)
    istree(x) ? operation(x) : x
end
function AbstractTrees.nodevalue(x::BasicSymbolic)
    if !istree(x)
        exprtype(x) => x
    elseif isadd(x)
        exprtype(x) => (scalar=x.coeff, coeffs=Tuple(k=>v for (k,v) in x.dict))
    elseif ismul(x)
        exprtype(x) => (scalar=x.coeff, powers=Tuple(k=>v for (k,v) in x.dict))
    else
        exprtype(x) => operation(x)
    end
end

function AbstractTrees.children(x::Symbolic)
    istree(x) ? arguments(x) : ()
end

"""
    inspect([io::IO=stdout], expr; hint=true)

Inspect an expression tree `expr`. Uses AbstractTrees to print out an expression.

BasicSymbolic expressions will print the Unityper type (ADD, MUL, DIV, POW, SYM, TERM) and the relevant internals as the head, and the children in the subsequent lines as accessed by `arguments`. Other types will get printed as subtrees.

Line numbers will be shown, use `pluck(expr, line_number)` to get the sub expression or leafnode starting at line_number.
"""
function inspect(io::IO, x::Symbolic; hint=true)
    lines = readlines(IOBuffer(sprint(io->AbstractTrees.print_tree(io, x))))
    digits = ceil(Int, log10(length(lines)))
    line_numbers = lpad.(string.(1:length(lines)), digits)
    print(io, join(string.(line_numbers, " ", lines), "\n"))
    hint && print(io, "\n\nHint: call SymbolicUtils.pluck(expr, line_number) to get the subexpression starting at line_number")
end

inspect(x::Symbolic; hint) = inspect(stdout, x; hint)

"""
    pluck(expr, n)

Pluck the `n`th subexpression from `expr` as given by pre-order DFS.
This is the same as the node numbering in `inspect`.
"""
function pluck(x, item)
    collect(Iterators.take(AbstractTrees.PreOrderDFS(x), item))[end]
end
