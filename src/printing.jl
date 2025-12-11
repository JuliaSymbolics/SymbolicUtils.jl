function Base.show(io::IO, x::BasicSymbolic{TreeReal})
    @match x begin
        BSImpl.Sym(; name) => Base.show_unquoted(io, name)
        BSImpl.Const(; val) => begin
            paren = val isa Union{Complex, Rational}
            if paren
                printstyled(io, "("; color = :blue)
            end
            printstyled(io, val; color = :blue)
            if paren
                printstyled(io, ")"; color = :blue)
            end
        end
        _ => show_term(io, x)
    end
end

function Base.show(io::IO, x::BasicSymbolic)
    @match x begin
        BSImpl.Sym(; name) => Base.show_unquoted(io, name)
        BSImpl.Const(; val) => begin
            paren = val isa Union{Complex, Rational}
            if paren
                printstyled(io, "("; color = :blue)
            end
            printstyled(io, val; color = :blue)
            if paren
                printstyled(io, ")"; color = :blue)
            end
        end
        BSImpl.ArrayOp(;) => show_arrayop(io, x)
        BSImpl.AddMul(; variant) => if variant === AddMulVariant.ADD
                show_add(io, x)
            else
                show_mul(io, x)
            end
        _ => show_term(io, x)
    end
end

show_term(io::IO, x::BasicSymbolic{TreeReal}) = show_call(io, operation(x), x)

function show_term(io::IO, x::BasicSymbolic)
    f = operation(x)
    if f === (+)
        show_add(io, x)
    elseif f === (*)
        show_mul(io, x)
    elseif f === (^)
        show_pow(io, x)
    elseif f === getindex
        show_ref(io, x)
    elseif f === identity && (arg = arguments(x)[1]; isconst(arg))
        show(io, arg)
    else
        show_call(io, f, x)
    end
end

function show_call(io::IO, @nospecialize(f), x::BasicSymbolic; @nospecialize(kw...))
    args = parent(arguments(x))
    len_args = length(args)
    fname = applicable(nameof, f)::Bool ? nameof(f)::Symbol : :_
    if Base.isunaryoperator(fname) && len_args == 1
        print(io, fname)
        print_arg(io, args[1])
        return
    end
    if Base.isbinaryoperator(fname) && len_args > 1
        @union_split_smallvec args begin
            for (i, t) in enumerate(args)
                i == 1 || print(io, " ", fname, " ")
                print_arg(io, t)
            end
        end
        return
    end
    Base.show(io, f)
    print(io, "(")
    @union_split_smallvec args begin
        for (i, t) in enumerate(args)
            print(io, t)
            i == len_args || print(io, ", ")
        end
    end
    if !isempty(kw)
        print(io, "; ")
        len_kwargs = length(kw)
        for (i, (k, v)) in enumerate(kw)
            print(io, k, " = ")
            print_arg(io, v)
            i == len_kwargs || print(io, ", ")
        end
    end
    print(io, ")")
end

function show_call(io::IO, @nospecialize(f::Mapper), x::BasicSymbolic{T}) where {T}
    _args = arguments(x)
    args = ArgsT{T}()
    sizehint!(args, length(_args) + 1)
    push!(args, BSImpl.Const{T}(f.f; unsafe = false))
    append!(args, _args)

    newx = BSImpl.Term{T}(map, args; type = Any, shape = ShapeVecT(), unsafe = false)
    show_call(io, map, newx)
end

function show_call(io::IO, @nospecialize(f::Mapreducer), x::BasicSymbolic{T}) where {T}
    _args = arguments(x)
    args = ArgsT{T}()
    sizehint!(args, length(_args) + 2)
    push!(args, BSImpl.Const{T}(f.f; unsafe = false))
    push!(args, BSImpl.Const{T}(f.reduce; unsafe = false))
    append!(args, _args)

    newx = BSImpl.Term{T}(mapreduce, args; type = Any, shape = ShapeVecT(), unsafe = false)
    if f.dims isa Colon && f.init === nothing
        show_call(io, mapreduce, newx)
    elseif f.dims isa Colon
        show_call(io, mapreduce, newx; init = f.init)
    elseif f.init === nothing
        show_call(io, mapreduce, newx; dims = f.dims)
    else
        show_call(io, mapreduce, newx; dims = f.dims, init = f.init)
    end
end

function show_pow(io::IO, x::BasicSymbolic)
    base, exp = @match x begin
        BSImpl.Term(; args) => args
    end
    if isnegative(base)
        print(io, "(")
        print(io, base)
        print(io, ")")
    else
        print_arg(io, base)
    end
    print(io, "^")
    print_arg(io, exp)
end

function show_ref(io::IO, var::BasicSymbolic)
    args = @match var begin
        BSImpl.Term(; args) => args
    end
    @union_split_smallvec args begin
        x = args[1]
        idx = @view(args[2:end])
        @match x begin
            BSImpl.Sym(; name) && if name === IDXS_SYM end => begin
                @assert length(idx) == 1
                print(io, "_", idx[1])
                return
            end
            _ => nothing
        end
        ic = iscall(x)
        ic && print(io, "(")
        print(io, x)
        ic && print(io, ")")
        print(io, "[")
        for (i, ii) in enumerate(idx)
            print_arg(io, ii)
            i == lastindex(idx) || print(io, ", ")
        end
        print(io, "]")
    end
end

function _isnegative(@nospecialize(val))
    if val isa Int
        return val < 0
    elseif val isa Int32
        return val < 0
    elseif val isa BigInt
        return val < 0
    elseif val isa Float64
        return val < 0
    elseif val isa Float32
        return val < 0
    elseif val isa BigFloat
        return val < 0
    elseif val isa Rational{Int}
        return val < 0
    elseif val isa Real
        return (val < 0)::Bool
    else
        return false
    end
end

function isnegative(x::BasicSymbolic)
    @match x begin
        BSImpl.Const(; val) => _isnegative(val)
        BSImpl.AddMul(; coeff, variant) && if variant === AddMulVariant.MUL end => _isnegative(coeff)
        _ => false
    end
end

print_arg(io::IO, x) = print(io, x)
function print_arg(io::IO, x::BasicSymbolic; paren = true)
    paren && iscall(x) && return print_arg(io, operation(x), x; paren)
    print(io, x)
end

function print_arg(io::IO, @nospecialize(f), x::BasicSymbolic; paren = true)
    paren || return print(io, x)
    iscall(f)::Bool && return print(io, x)

    if f === (*) || f === (+) || f === (^) || f === (/) || (applicable(nameof, f)::Bool && Base.isbinaryoperator(nameof(f)::Symbol)::Bool)
        print(io, "(", x, ")")
    else
        print(io, x)
    end
end

function remove_minus(t::BasicSymbolic{T}) where {T}
    @match t begin
        BSImpl.Const(; val) => return BSImpl.Const{T}(-val; unsafe = false)
        BSImpl.AddMul(; coeff, dict, type, shape, variant) && if variant === AddMulVariant.MUL end => begin
            return BSImpl.AddMul{T}(-coeff, dict, variant; type, shape, unsafe = false)
        end
    end
end

function show_add(io::IO, x::BasicSymbolic)
    show_add(io, parent(sorted_arguments(x)))
end

function show_add(io::IO, args::ArgsT{T}) where {T}
    @union_split_smallvec args begin
        for (i, t) in enumerate(args)
            neg = isnegative(t)
            if i == 1
                neg && print(io, "-")
            else
                print(io, neg ? " - " : " + ")
            end
            if !neg
                show(io, t)
                continue
            end
            @match t begin
                BSImpl.Const(; val) => show(io, BSImpl.Const{T}(-val; unsafe = true))
                BSImpl.AddMul(;) => begin
                    args = copy(parent(sorted_arguments(t)))
                    @union_split_smallvec args begin
                        args[1] = BSImpl.Const{T}(-unwrap_const(args[1]); unsafe = true)
                    end
                    show_mul(io, args)
                end
            end
        end
    end
end

function _isminus(@nospecialize(val))
    if val isa Int
        return val == -1
    elseif val isa Int32
        return val == -1
    elseif val isa BigInt
        return val == -1
    elseif val isa Float64
        return val == -1
    elseif val isa Float32
        return val == -1
    elseif val isa BigFloat
        return val == -1
    elseif val isa Rational{Int}
        return val == -1
    elseif val isa Number
        return (val == -1)::Bool
    else
        return false
    end
end
function _isunit(@nospecialize(val))
    if val isa Int
        return val == 1
    elseif val isa Int32
        return val == 1
    elseif val isa BigInt
        return val == 1
    elseif val isa Float64
        return val == 1
    elseif val isa Float32
        return val == 1
    elseif val isa BigFloat
        return val == 1
    elseif val isa Rational{Int}
        return val == 1
    elseif val isa Number
        return (val == 1)::Bool
    else
        return false
    end
end

function _is_paren_scalar(@nospecialize(x))
    return x isa Complex && !iszero(imag(x))::Bool || x isa Rational || x isa Number && !isfinite(x)::Bool
end

function isnumberconst(x::BasicSymbolic)
    @match x begin
        BSImpl.Const(; val) => val isa Number
        _ => false
    end
end

function show_mul(io::IO, x::BasicSymbolic)
    show_mul(io, parent(sorted_arguments(x)))
end

function show_mul(io::IO, args::ArgsT{T}) where {T}
    length(args) == 1 && return print_arg(io, args[1])

    arg1 = args[1]
    arg2 = args[2]
    isminus = @match arg1 begin
        BSImpl.Const(; val) => _isminus(val)
        _ => false
    end
    isunit = @match arg1 begin
        BSImpl.Const(; val) => _isunit(val)
        _ => false
    end
    isparenscalar = @match arg1 begin
        BSImpl.Const(; val) => _is_paren_scalar(val)
        _ => false
    end
    nostar = isminus || isunit || (!isparenscalar && isnumberconst(arg1) && !isnumberconst(arg2))

    @union_split_smallvec args begin
        for (i, t) in enumerate(args)
            if i == 1
                if isminus
                    print(io, "-")
                elseif !isunit
                    print_arg(io, t)
                end
                continue
            end
            if !(i == 2 && nostar)
                print(io, "*")
            end
            print_arg(io, t)
        end
    end
end

const SHOW_ARRAYOP = Ref{Bool}(false)
function show_arrayop(io::IO, aop::BasicSymbolic)
    @match aop begin
        BSImpl.ArrayOp(; output_idx, expr, term, reduce, ranges) => begin
            if !SHOW_ARRAYOP[] && term !== nothing && iscall(term)
                return show(io, term)
            end
            print(io, "@arrayop")
            print(io, "(_[$(join(string.(output_idx), ","))] := $(expr))")
            if reduce != +
                print(io, " ($(reduce))")
            end

            if !isempty(ranges)
                print(io, " ", join(["$k in $v" for (k, v) in ranges], ", "))
            end
        end
    end
end

