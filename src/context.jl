struct EmptyCtx end

(ctx::EmptyCtx)(x; kwargs...) = x

struct IfElseCtx{F, A, B}
    cond::F
    yes::A
    no::B
end

function (ctx::IfElseCtx)(x; kwargs...)
    ctx.cond(x; kwargs...) ?  ctx.yes(x; kwargs...) : ctx.no(x; kwargs...)
end

struct ChainCtx{Cs}
    ctxs::Cs
end

function (ctx::ChainCtx)(@nospecialize(x); kwargs...)
    for f in ctx.ctxs
        y = f(x)
        if y !== nothing
            x = y
        end
    end
    return x
end

struct FixpointCtx{C}
    ctx::C
end

function (ctx::FixpointCtx)(x; kwargs...)
    y = ctx.ctx(x; kwargs...)
    while x !== y && !isequal(x, y)
        y = ctx.ctx(x; kwargs...)
        isnothing(y) && return x
        x = y
    end
    return x
end

struct BoolCtx end

(::BoolCtx)(x; kwargs...) = @rule(~x::sym_isa(Bool) => BOOLEAN_RULES(~x, applyall=true, recurse=true))(x)

struct NumberCtx end

(::NumberCtx)(x; kwargs...) = @rule(~x::sym_isa(Number) => NUMBER_RULES(~x, applyall=true, recurse=true))(x)

struct TrigCtx end

(::TrigCtx)(x; kwargs...) = @rule(~x::sym_isa(Number) => TRIG_RULES(~x, applyall=true, recurse=true))(x)

# TODO: make Fixpoint efficient and use it for each.
RulesCtx() = IfElseCtx((x; kwargs...)->has_trig(x),
                       FixpointCtx(ChainCtx((NumberCtx(), TrigCtx(), BoolCtx()))),
                       FixpointCtx(ChainCtx((NumberCtx(), BoolCtx()))))


struct PolyNFCtx end

function (::PolyNFCtx)(x; kwargs...)
    to_term(to_mpoly(x)...)
end

DefaultCtx() = ChainCtx((PolyNFCtx(), RulesCtx())) # TODO: Fixpoint?

simplify2(x, ctx=RulesCtx(); kwargs...) = ctx(x; kwargs...)


struct PrewalkCtx{C}
    ctx::C
end

function (p::PrewalkCtx)(x; kwargs...)
    if istree(x)
        t = Term{symtype(x)}(operation(x),
                         map(t->p.ctx(t; kwargs...), arguments(x)))
        return p.ctx(t)
    else
        return p.ctx(x)
    end
end

RuleSetCtx(rs) = FixpointCtx(PrewalkCtx(ChainCtx(rs)))

