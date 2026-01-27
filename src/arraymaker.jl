const INVALID_MAKEARRAY_DEFINITION_MSG = """
The `@makearray` definition must be of the form `ident[start1:stop1, start2:stop2, ...]`.
"""

const INVALID_MAKEARRAY_SEQ_MSG = """
The LHS of each sequence entry in `@makearray` must be of the form \
`ident[start1:stop1, start2:stop2, ...]`.
"""

"""
    @makearray arr[shape...] begin
        arr[subarray...] => value
        # ...
    end

Construct an `ArrayMaker`. `ArrayMaker` symbolically represents an array
composed of blocks of other arrays. To demonstrate, consider the following example:

```julia
@syms x[1:3]::Real y[1:3]::Real z[1:3]::Real
w = @makearray foo[1:3, 1:3] begin
    foo[1:1, 1:3] => x'
    foo[2:2, 1:3] => @arrayop (1, i) y[i] + z[i]
    foo[3:3, 1:1] => [1;;]
    foo[3:3, 2:2] => [z[1];;]
    foo[3:3, 3:3] => [z'z;;]
end
```

The first argument to `@makearray` is an indexing expression denoting the shape of the
constructed array. The identifier used here (`foo`) is arbitrary. It has no bearing
on the result, and is only used as part of the macro syntax inside the `begin..end` block.

Each entry in the `begin..end` block is a pair denoting a subarray to assign, and the
value to assign it. Note that each subarray thus assigned must have the same number
of dimensions as the created array. In other words, inside the block `foo` can only be
indexed using ranges with a unit step (`UnitRange{Int}`). `foo[3, 1] => 1` is invalid
syntax and will error. The RHS of each pair (the value assigned to the subarray) must have
the same size as the subarray. Extra unit dimensions must be added as necessary, for
example via the `1` in `@arrayop (1, i) y[i] + z[i]`. The identifier `foo` has no
meaning if used in the RHS. It will simply refer to a variable named `foo` in the current
scope, if such a variable exists.

For convenience, `ArrayMaker` and `@makearray` allow assigning overlapping ranges. In such
cases, later assignments in `@makearray` override earlier ones. For example:

```julia
q = @makearray q[1:3] begin
    q[1:3] => x
    q[2:3] => y[1:2]
end
```

Here, `q` represents the array `[x[1], y[1], y[2]]`.

Nesting `@makearray` is permitted. The following is valid syntax:

```julia
w = @makearray w[1:3, 1:3] begin
    w[1:1, 1:3] => x'
    w[2:2, 1:3] => @makearray _[1:1, 1:3] begin
        _[1:1, 1:1] => [y[1];;]
        _[1:1, 2:3] => z'[:, 1:2]
    end
    w[3:3, 1:1] => [1;;]
    w[3:3, 2:2] => [z[1];;]
    w[3:3, 3:3] => [z'z;;]
end
```
"""
macro makearray(definition::Expr, sequence::Expr)
    shape = get_shape_from_ref_expr(definition, INVALID_MAKEARRAY_DEFINITION_MSG)
    regions = Expr[]
    values = Expr[]

    @assert Meta.isexpr(sequence, :block) """
    The `@makearray` sequence must be a `begin..end` block.
    """
    sequence = sequence::Expr
    for entry in sequence.args
        entry isa LineNumberNode && continue
        @assert Meta.isexpr(entry, :call) && (entry::Expr).args[1] == :(=>) """
        Each entry in the `@makearray` sequence must be of the form \
        `ident[start1:stop1, ...] => value`. Found $entry, which does not have `=>` as \
        the operation.
        """
        entry = entry::Expr
        region = get_shape_from_ref_expr(entry.args[2], INVALID_MAKEARRAY_SEQ_MSG, true)
        value = entry.args[3]
        push!(regions, region)
        push!(values, esc(value))
    end

    @assert length(regions) == length(values)
    innerhead = length(regions) <= 10 ? :tuple : :vect
    regions_expr = Expr(:call, RegionsT, tuple_or_vect(regions, innerhead))
    values_expr = tuple_or_vect(values, innerhead)

    result = :(let shape = $shape, values = $values_expr
        vartype = $vartype_from_values(values)
        regions = $regions_expr
        $ArrayMaker{vartype}(regions, values; shape)
    end)

    return result
end

function get_shape_from_ref_expr(def::Expr, err::String, parse_begin_end = false)
    @assert Meta.isexpr(def, :ref) err

    shape_tuple = Expr(:tuple)
    sizehint!(shape_tuple.args, length(def.args) - 1)
    for (i, arg) in enumerate(Iterators.drop(def.args, 1))
        @assert Meta.isexpr(arg, :call) && (arg::Expr).args[1] === :(:) err
        arg = arg::Expr
        @assert length(arg.args) == 3 """
        The ranges in `@makearray` must be unit ranges. They cannot have an explicit step \
        size. Found invalid range $arg.
        """
        if parse_begin_end
            arg = :(let var"begin" = $first(shape[$i]), var"end" = $last(shape[$i])
                        $(esc(arg))
                    end)
        else
            arg = esc(arg)
        end
        push!(shape_tuple.args, arg)
    end
    shape_expr = Expr(:call, ShapeVecT, shape_tuple)
    return shape_expr
end

function tuple_or_vect(vals::Vector{Expr}, innerhead::Symbol)
    vals_expr = Expr(innerhead)
    append!(vals_expr.args, vals)
    return vals_expr
end

function _vartype_from_values()
    error("""
    Could not infer vartype from `@arraymaker` macro usage. All values in the sequence \
    are not symbolic. Wrap at least one of the values in a `SymbolicUtils.Const` of the \
    appropriate vartype.
    """)
end
_vartype_from_values(::BasicSymbolic{T}, _...) where {T} = T
_vartype_from_values(fst, rest...) = _vartype_from_values(rest...)
vartype_from_values(vals::Tuple) = _vartype_from_values(vals...)
vartype_from_values(vals::Vector{BasicSymbolic{T}}) where {T} = T
function vartype_from_values(@nospecialize(vals::Vector))
    for val in vals
        if val isa BasicSymbolic{SymReal}
            return SymReal
        elseif val isa BasicSymbolic{SafeReal}
            return SafeReal
        elseif val isa BasicSymbolic{TreeReal}
            return TreeReal
        end
    end
    _vartype_from_values()
end
