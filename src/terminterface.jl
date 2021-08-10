TermInterface.isterm(t::Type{<:Sym}) = false
TermInterface.isterm(t::Type{<:Symbolic}) = true

TermInterface.gethead(t::Symbolic) = :call 
TermInterface.gethead(t::Sym) = t
TermInterface.getargs(t::Symbolic) = [operation(t), arguments(t)...]
TermInterface.arity(t::Symbolic) = length(arguments(t))
