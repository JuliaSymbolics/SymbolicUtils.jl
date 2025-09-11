const IDXS_SYM = :𝑖ᵢₓ
const IDXS_SYMREAL = Sym{SymReal}(IDXS_SYM; type = Vector{Int}, shape = Unknown(1))
const IDXS_SAFEREAL = Sym{SafeReal}(IDXS_SYM; type = Vector{Int}, shape = Unknown(1))
const IDXS_TREEREAL = Sym{TreeReal}(IDXS_SYM; type = Vector{Int}, shape = Unknown(1))

idxs_for_arrayop(::Type{SymReal}) = IDXS_SYMREAL
idxs_for_arrayop(::Type{SafeReal}) = IDXS_SAFEREAL
idxs_for_arrayop(::Type{TreeReal}) = IDXS_TREEREAL

"""
    @arrayop (idxs...,) expr [idx in range, ...] [options...]

Construct a vectorized array operation using Tullio.jl-like generalized Einstein notation.
`idxs` is a tuple corresponding to the indices in the result. `expr` is the indexed
expression. Indices used in `expr` not present in `idxs` will be collapsed using the
`reduce` function, which defaults to `+`. For example, matrix multiplication can be
expressed as follows:

```julia
@syms A[1:5, 1:5] B[1:5, 1:5]
matmul = @arrayop (i, j) A[i, k] * B[k, j]
```

Here the elements of the collapsed dimension `k` are reduced using the `+` operation. To
use a different reducer, the `reduce` option can be supplied:

```julia
C = @arrayop (i, j) A[i, k] * B[k, j] reduce=max
```

Now, `C[i, j]` is the maximum value of `A[i, k] * B[k, j]` for across all `k`.

# Singleton dimensions

Arbitrary singleton dimensions can be added in the result by inserting `1` at the desired
position in `idxs`:

```julia
C = @arrayop (i, 1, j, 1) A[i, k] * B[k, j]
```

Here, `C` is a symbolic array of size `(5, 1, 5, 1)`.

# Restricted ranges

For any index variable `i` in `expr`, all its usages in `expr` must correspond to axes of
identical length. For example:

```julia
@syms D[1:3, 1:5]
@arrayop (i, j) A[i, k] * D[k, j]
```

The above usage is invalid, since `k` in `A` is used to index an axis of length `5` and in
`D` is used to index an axis of length `3`. The iteration range of variables can be manually
restricted:

```julia
@arrayop (i, j) A[i, k] * D[k, j] k in 1:3
```

This expression is valid. Note that when manually restricting iteration ranges, the range
must be a subset of the axes where the iteration variable is used. Here `1:3` is a subset
of both `1:5` and `1:3`.

# Axis offsets

The usages of index variables can be offset.

```julia
A2 = @arrayop (i, j) A[i + 1, j] + A[i, j + 1]
```

Here, `A2` will have size `(4, 4)` since SymbolicUtils.jl is able to recognize that `i` and
`j` can only iterate in the range `1:4`. For trivial offsets of the form `idx + offset`
(`offset` can be negative), the bounds of `idx` can be inferred. More complicated offsets
can be used, but this requires manually specifying ranges of the involved index variables.

```julia
A3 = @arrayop (i, j) A[2i - 1, j] i in 1:3
```

In this scenario, it is the responsibility of the user to ensure the arrays are always
accessed within their bounds.

# Usage with non-standard axes

The index variables are "idealized" indices. This means that as long as the length of
all axes where an index variable is used is identical, the bounds of the axes are
irrelevant.

```julia
@syms E[0:4, 0:4]
F = @arrayop (i, j) A[i, k] * E[k, j]
```

Despite `axes(A, 2)` being `1:5` and `axes(E, 1)` being `0:4`, the above expression is
valid since `length(1:5) == 5 == length(0:4)`. When generating code, index variables will
be appropriately offset to index the involved axes.

If the range of an index variable is manually specified, the index variable is no longer
"idealized" and the user is responsible for offsetting appropriately. The above example
with a manual range for `k` should be written as:

```julia
F2 = @arrayop (i, j) A[i, k] * E[k - 1, j] k in 1:5
```

# Result shape

The result is always 1-indexed with axes of appropriate lengths, regardless of the shape of
the inputs.
"""
macro arrayop(output_idx, expr, options...)
    rs = []
    reduce = +
    call = nothing

    extra = []
    for o in options
        if Meta.isexpr(o, :call) && o.args[1] == :in
            push!(rs, :($(o.args[2]) => $(o.args[3])))
        elseif Meta.isexpr(o, :(=)) && o.args[1] == :reduce
            reduce = o.args[2]
        elseif Meta.isexpr(o, :(=)) && o.args[1] == :term
            call = o.args[2]
        else
            push!(extra, o)
        end
    end
    @assert output_idx.head == :tuple

    oidxs = filter(x->x isa Symbol, output_idx.args)
    iidxs = find_indices(expr)
    vartype_ref = find_vartype_reference(expr)
    idxs  = union(oidxs, iidxs)
    fbody = call2term(deepcopy(expr))
    oftype(x,T) = :($x::$T)

    let_assigns = Expr(:block)
    push!(let_assigns.args, Expr(:(=), :__vartype, :($vartype($vartype_ref))))
    push!(let_assigns.args, Expr(:(=), :__idx, :($idxs_for_arrayop(__vartype))))
    for (i, idx) in enumerate(idxs)
        push!(let_assigns.args, Expr(:(=), idx, :(__idx[$i])))
    end
    push!(let_assigns.args, Expr(:(=), :__expr, fbody))
    push!(let_assigns.args, Expr(:(=), :__output_idx, :($OutIdxT{__vartype}($output_idx))))
    push!(let_assigns.args, Expr(:(=), :__ranges, :($RangesT{__vartype}($(rs...)))))
    return Expr(:let, let_assigns, quote
        $ArrayOp{__vartype}(__output_idx,
                 __expr,
                 $reduce,
                 $(call2term(call)),
                 __ranges)
    end) |> esc
end

function find_indices(expr, idxs=[])
    !(expr isa Expr) && return idxs
    if expr.head == :ref
        return append!(idxs, filter(x->x isa Symbol, expr.args[2:end]))
    elseif expr.head == :call && expr.args[1] == :getindex || expr.args[1] == getindex
        return append!(idxs, filter(x->x isa Symbol, expr.args[3:end]))
    else
        foreach(x->find_indices(x, idxs), expr.args)
        return idxs
    end
end

function find_vartype_reference(expr)
    !(expr isa Expr) && return nothing
    if expr.head == :ref
        return expr.args[1]
    elseif expr.head == :call && (expr.args[1] == :getindex || expr.args[1] === getindex)
        return expr.args[2]
    end
    for arg in expr.args
        res = find_vartype_reference(arg)
        res === nothing || return res
    end
    return nothing
end

function call2term(expr, arrs=[])
    !(expr isa Expr) && return :($unwrap($expr))
    if expr.head == :call
        if expr.args[1] == :(:)
            return expr
        end
        return Expr(:call, term, map(call2term, expr.args)...)
    elseif expr.head == :ref
        return Expr(:ref, call2term(expr.args[1]), expr.args[2:end]...)
    elseif expr.head == Symbol("'")
        return Expr(:call, term, adjoint, map(call2term, expr.args)...)
    end

    return Expr(expr.head, map(call2term, expr.args)...)
end
