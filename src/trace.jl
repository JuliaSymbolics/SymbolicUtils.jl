using Mjolnir, IRTools, Base.Meta
using Mjolnir: Const, trace
using IRTools: xcall, argument!, return!
import IRTools: IR, func

export @symbolic, IR, func

tracetype(s::Symbolic{T}) where {T} = T
function tracetype(s::Symbolic{T}) where {T<:AbstractArray}
    @maybe s = shape(s) return Mjolnir.Shape{T}(length.(s.axes))
    return T
end
tracetype(s) = Const(s)

macro symbolic(ex)
    @assert ex.head == :call

    f = ex.args[1]
    args = ex.args[2:end]
    Ts = map(x->:(tracetype($(esc(x)))), args[1:end-1])
    if !isempty(args) &&
        args[end] isa Expr &&
        args[end].head == :(...)

        Ts = vcat(Ts, :(tracetype.($(esc(args[end].args[1])))...))
    else
        Ts = vcat(Ts, :(tracetype($(esc(args[end])))))
    end

    quote
        f = $(esc(f))

        ir = trace(Mjolnir.Multi(SymArrayPrimitives(), Mjolnir.Defaults()), Const(f), $(Ts...))
        irterm(ir, [$(esc.(args)...)])
    end
end

irterm(ir::IR, v, args) = v

function irterm(ir::IR, v::IRTools.Variable, args)
    arg = findfirst(==(v), IRTools.arguments(ir))
    arg != nothing && return args[arg-1] # given as an argument

    ex = ir[v].expr # computed on this line
    if isexpr(ex, :call)
        #TODO: use type info from mjolnir
        #using Term here uses promote_symtype from Symutils to figure out output type
        f = irterm(ir, ex.args[1], args)
        args = irterm.((ir,), ex.args[2:end], (args,))
        return Term(f, [args...])
    else
        return ex
    end
end

irterm(ir::IR, args) = irterm(ir, IRTools.returnvalue(IRTools.blocks(ir)[end]), args)

to_ir!(s, ir, mod, varmap) = s

function to_ir!(s::Sym, ir, mod, varmap)
    haskey(varmap, s) ? varmap[s] : GlobalRef(mod, nameof(s))
end

function to_ir!(t::Term, ir,  mod, varmap)
    haskey(varmap, t) && return varmap[t]
    inps = [to_ir!(x, ir, mod, varmap) for x in arguments(t)]
    push!(ir, xcall(operation(t), inps...))
end

function IR(t::Term, args; mod=Main)
    ir = IR()
    varmap = Dict()
    for v in args
        mv = argument!(ir)
        varmap[v] = mv
    end

    res = to_ir!(t, ir, mod, varmap)
    return!(ir, res)
    ir
end
