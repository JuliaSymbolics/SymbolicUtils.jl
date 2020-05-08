using Mjolnir, IRTools, Base.Meta
using Mjolnir: Const, trace
using IRTools: IR

export @symbolic

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

irterm(ir::IR, v, args) = v

function irterm(ir::IR, v::IRTools.Variable, args)
  arg = findfirst(==(v), IRTools.arguments(ir))
  arg == nothing || return args[arg-1]
  ex = ir[v].expr
  if isexpr(ex, :call)
    return ex.args[1](irterm.((ir,), ex.args[2:end], (args,))...)
  else
    return ex
  end
end

irterm(ir::IR, args) = irterm(ir, IRTools.returnvalue(IRTools.blocks(ir)[end]), args)

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
