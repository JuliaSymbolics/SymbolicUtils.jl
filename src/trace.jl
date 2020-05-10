using Mjolnir, IRTools, Base.Meta
using Mjolnir: Const, trace
using IRTools: xcall, argument!, return!
import IRTools: IR, func

export @symbolic, IR, func

tracetype(s::Symbolic{T}) where {T} = T
tracetype(s) = Const(s)

macro symbolic(ex)
    f = ex.args[1]
    args = ex.args[2:end]
    Ts = map(x->:(tracetype($(esc(x)))), args)
    quote
        f = $(esc(f))
        ir = trace(Mjolnir.Defaults(), Const(f), $(Ts...))
        irterm(ir, $args)
    end
end

irterm(ir::IR, v, args) = v

function irterm(ir::IR, v::IRTools.Variable, args)
    arg = findfirst(==(v), IRTools.arguments(ir))
    arg != nothing && return args[arg-1]
    ex = ir[v].expr
    if isexpr(ex, :call)
        return term(irterm.((ir,), ex.args, (args,))...)
    else
        return ex
    end
end

irterm(ir::IR, args) = irterm(ir, IRTools.returnvalue(IRTools.blocks(ir)[end]), args)

function to_mjolnir!(s::Sym, ir, mod, varmap)
    haskey(varmap, s) ? varmap[s] : GlobalRef(mod, nameof(s))
end

function to_mjolnir!(t::Term, ir,  mod, varmap)
    inps = [to_mjolnir!(x, ir, mod, varmap) for x in arguments(t)]
    push!(ir, xcall(operation(t), inps...))
end

function IR(t::Term, args; mod=Main)
    ir = IR()
    varmap = Dict()
    for v in args
        mv = argument!(ir)
        varmap[v] = mv
    end

    res = to_mjolnir!(t, ir, mod, varmap)
    return!(ir, res)
    ir
end
