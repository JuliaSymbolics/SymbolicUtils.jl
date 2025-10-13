const show_simplified = Ref(false)

isnegative(t::Real) = t < 0
function isnegative(t)
    if iscall(t) && operation(t) === (*)
        coeff = first(arguments(t))
        return isnegative(unwrap_const(coeff))
    end
    return false
end

# Term{}
print_arg(io, x::Union{Complex, Rational}; paren=true) = print(io, "(", x, ")")
function isbinop(f)
    iscall(f) && !iscall(operation(f)) && applicable(nameof, operation(f)) &&
        Base.isbinaryoperator(nameof(operation(f)))
end
function print_arg(io, x; paren=false)
    if paren && isbinop(x)
        print(io, "(", x, ")")
    else
        print(io, x)
    end
end
print_arg(io, s::String; paren=true) = show(io, s)
function print_arg(io, f, x)
    f !== (*) && return print_arg(io, x)
    if Base.isbinaryoperator(nameof(f))
        print_arg(io, x, paren=true)
    else
        print_arg(io, x)
    end
end

function remove_minus(t)
    !iscall(t) && return -t
    @assert operation(t) == (*)
    args = sorted_arguments(t)
    @assert unwrap_const(args[1]) < 0
    Any[-unwrap_const(args[1]), args[2:end]...]
end


function show_add(io, args)
    for (i, t) in enumerate(args)
        neg = isnegative(t)
        if i != 1
            print(io, neg ? " - " : " + ")
        elseif isnegative(t)
            print(io, "-")
        end
        if neg
            show_mul(io, remove_minus(t))
        else
            print_arg(io, +, t)
        end
    end
end

function show_pow(io, args)
    base, ex = args
    base = unwrap_const(base)
    ex = unwrap_const(ex)
    if base isa Real && base < 0
        print(io, "(")
        print_arg(io, base)
        print(io, ")")
    else
        print_arg(io, base, paren=true)
    end
    print(io, "^")
    print_arg(io, ex, paren=true)
end

function show_mul(io, args)
    length(args) == 1 && return print_arg(io, *, args[1])

    arg1 = unwrap_const(args[1])
    arg2 = unwrap_const(args[2])
    minus = arg1 isa Number && arg1 == -1
    unit = arg1 isa Number && arg1 == 1

    paren_scalar = (arg1 isa Complex && !_iszero(imag(arg1))) ||
                   arg1 isa Rational ||
                   (arg1 isa Number && !isfinite(arg1))

    nostar = minus || unit ||
            (!paren_scalar && unwrap_const(arg1) isa Number && !(arg2 isa Number))

    for (i, t) in enumerate(args)
        if i != 1
            if i==2 && nostar
            else
                print(io, "*")
            end
        end
        if i == 1 && minus
            print(io, "-")
        elseif i == 1 && unit
        else
            print_arg(io, *, t)
        end
    end
end

function show_ref(io, f, args)
    x = args[1]
    idx = args[2:end]
    if issym(x) && nameof(x) == IDXS_SYM
        @assert length(idx) == 1
        print(io, "_", idx[1])
        return
    end
    iscall(x) && print(io, "(")
    print(io, x)
    iscall(x) && print(io, ")")
    print(io, "[")
    for i=1:length(idx)
        print_arg(io, idx[i])
        i != length(idx) && print(io, ", ")
    end
    print(io, "]")
end

function show_call(io, f, args)
    if f isa Mapper
        return show_call(io, map, [[f.f]; args])
    end
    if f isa Mapreducer
        return show_call(io, mapreduce, [[f.f, f.reduce]; args])
    end
    fname = iscall(f) ? Symbol(repr(f)) : nameof(f)
    len_args = length(args)
    if Base.isunaryoperator(fname) && len_args == 1
        print(io, "$fname")
        print_arg(io, first(args), paren=true)
    elseif Base.isbinaryoperator(fname) && len_args > 1
        for (i, t) in enumerate(args)
            i != 1 && print(io, " $fname ")
            print_arg(io, t, paren=true)
        end
    else
        if issym(f)
            Base.show_unquoted(io, nameof(f))
        else
            Base.show(io, f)
        end
        print(io, "(")
        for i=1:length(args)
            print(io, args[i])
            i != length(args) && print(io, ", ")
        end
        print(io, ")")
    end
end

function show_term(io::IO, t)
    if get(io, :simplify, show_simplified[])
        return print(IOContext(io, :simplify=>false), simplify(t))
    end

    f = operation(t)
    args = sorted_arguments(t)
    if vartype(t) === TreeReal
        show_call(io, f, args)
    elseif f === (+)
        show_add(io, args)
    elseif f === (*)
        show_mul(io, args)
    elseif f === (^)
        show_pow(io, args)
    elseif f === (getindex)
        show_ref(io, f, args)
    elseif f === (identity) && !issym(args[1]) && !iscall(args[1])
        show(io, args[1])
    else
        show_call(io, f, args)
    end

    return nothing
end

const SHOW_ARRAYOP = Ref{Bool}(false)
function show_arrayop(io::IO, aop::BasicSymbolic)
    if iscall(aop.term) && !SHOW_ARRAYOP[]
        show(io, aop.term)
    else
        print(io, "@arrayop")
        print(io, "(_[$(join(string.(aop.output_idx), ","))] := $(aop.expr))")
        if aop.reduce != +
            print(io, " ($(aop.reduce))")
        end

        if !isempty(aop.ranges)
            print(io, " ", join(["$k in $v" for (k, v) in aop.ranges], ", "))
        end
    end
end

"""
    showraw([io::IO], t)

Display the raw structure of a symbolic expression without simplification.

This function shows the internal structure of symbolic expressions without applying
any simplification rules, which is useful for debugging and understanding the
exact form of an expression.

# Arguments
- `io::IO`: Optional IO stream to write to (defaults to stdout)
- `t`: The symbolic expression to display

# Examples
```julia
julia> @syms x
x

julia> expr = x + x + x
3x

julia> showraw(expr)  # Shows the unsimplified structure
x + x + x
```
"""
showraw(io, t) = Base.show(IOContext(io, :simplify=>false), t)
showraw(t) = showraw(stdout, t)

function Base.show(io::IO, v::BSImpl.Type)
    if issym(v)
        Base.show_unquoted(io, v.name)
    elseif isconst(v)
        v = unwrap_const(v)
        if v isa Complex
            printstyled(io, "("; color = :blue)
        end
        printstyled(io, v; color = :blue)
        if v isa Complex
            printstyled(io, ")"; color = :blue)
        end
    elseif isarrayop(v)
        show_arrayop(io, v)
    else
        show_term(io, v)
    end
end

