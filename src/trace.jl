using Mjolnir, IRTools, Base.Meta
using Mjolnir: Const, trace
using IRTools: IR, xcall, func, argument!

export @symbolic, to_mjolnir, func

collect_names(x, names) = return

collect_names(x::Symbol, names) = push!(names, (x, :Float64))

function collect_names(x::Expr, names)
    if isexpr(x, :(::)) && x.args[1] isa Symbol
        push!(names, (x.args[1], x.args[2]))
    elseif isexpr(x, :call)
        foreach(x -> collect_names(x, names), x.args[2:end])
    else
        foreach(x -> collect_names(x, names), x.args)
    end
end

function collect_names(x)
    names = []
    collect_names(x, names)
    return names
end

macro symbolic(ex)
    names = collect_names(ex)
    Ts = [T for (x, T) in names]
    f = :(($(first.(names)...),) -> $ex)
    quote
        f = $(esc(f))
        ir = trace(Mjolnir.Defaults(), Const(f), $(esc.(Ts)...))
        syms = ($([:(Sym{$(esc(T))}($(QuoteNode(name)))) for (name, T) in names]...),)
        irterm(ir, syms)
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

    to_mjolnir!(t, ir, mod, varmap)
    ir
end

func(t::Term, args) = func(IR(t,args))
