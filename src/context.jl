struct EmptyCtx end

(ctx::EmptyCtx)(x) = x

struct IfElseCtx{F, A, B}
    cond::F
    yes::A
    no::B
end

function (ctx::IfElseCtx)(x)
    ctx.cond(x) ?  ctx.yes(x) : ctx.no(x)
end

IfCtx(f, x) = IfElseCtx(f, x, EmptyCtx())

struct ChainCtx{Cs}
    ctxs::Cs
end

function (ctx::ChainCtx)(x)
    for f in ctx.ctxs
        y = @timer Base.@get!(rule_repr, f, repr(f)) f(x)
        if y !== nothing
            x = y
        end
    end
    return x
end

struct RestartedChain{Cs}
    ctxs::Cs
end

function (ctx::RestartedChain)(x)
    for f in ctx.ctxs
        y = @timer Base.@get!(rule_repr, f, repr(f)) f(x)
        if y !== nothing
            return ChainCtx(ctx.ctxs)(y)
        end
    end
    return x
end

struct FixpointCtx{C}
    ctx::C
end

function (ctx::FixpointCtx)(x)
    f = ctx.ctx
    y = @timer Base.@get!(rule_repr, f, repr(f)) f(x)
    while x !== y && !isequal(x, y)
        isnothing(y) && return x
        x = y
        y = @timer Base.@get!(rule_repr, f, repr(f)) f(x)
    end
    return x
end

struct PrewalkCtx{C}
    ctx::C
end

function (p::PrewalkCtx)(x)
    if istree(x)
        t = Term{symtype(x)}(operation(x),
                             map(t->(a = p(t); isnothing(a) ? t : a),
                                 arguments(x)))
        return p.ctx(t)
    else
        return p.ctx(x)
    end
end

BoolCtx() = IfCtx((x)->symtype(x) <: Bool, PrewalkCtx(ChainCtx(BOOLEAN_RULES2)))
NumberCtx() = IfCtx((x)->symtype(x) <: Number, numrules())
TrigCtx() = IfCtx((x)->has_trig(x), PrewalkCtx(ChainCtx(TRIG_RULES2)))

# TODO: make Fixpoint efficient and use it for each.
RulesCtx() = FixpointCtx(ChainCtx((NumberCtx(), TrigCtx(), BoolCtx())))


struct PolyNFCtx end

function (::PolyNFCtx)(x)
    to_term(to_mpoly(x)...)
end

DefaultCtx() = ChainCtx((PolyNFCtx(), RulesCtx())) # TODO: Fixpoint?


simplify2(x, ctx=RulesCtx()) = ctx(x)


function numrules()
    [ChainCtx(ASSORTED_RULES2),
     IfCtx((x;kw...)->is_operation(+)(x),
           ChainCtx(PLUS_RULES2)),
     IfCtx((x;kw...)->is_operation(*)(x),
           ChainCtx(TIMES_RULES2)),
     IfCtx((x;kw...)->is_operation(^)(x),
           ChainCtx(POW_RULES2))] |> RestartedChain |> PrewalkCtx
end

const NUMBER_RULES2 = [
    @rule ~t               => ASSORTED_RULES2(~t)
    @rule ~t::is_operation(+) =>  PLUS_RULES2(~t)
    @rule ~t::is_operation(*) => TIMES_RULES2(~t)
    @rule ~t::is_operation(^) =>   POW_RULES2(~t)
]

const PLUS_RULES2 = [
    @rule(+(~~x::isnotflat(+)) => flatten_term(+, ~~x))
    @rule(+(~~x::!(issortedₑ)) => sort_args(+, ~~x))
    @acrule(~a::isnumber + ~b::isnumber => ~a + ~b)

    @acrule(*(~~x) + *(~β, ~~x) => *(1 + ~β, (~~x)...))
    @acrule(*(~α, ~~x) + *(~β, ~~x) => *(~α + ~β, (~~x)...))
    @acrule(*(~~x, ~α) + *(~~x, ~β) => *(~α + ~β, (~~x)...))

    @acrule(~x + *(~β, ~x) => *(1 + ~β, ~x))
    @acrule(*(~α::isnumber, ~x) + ~x => *(~α + 1, ~x))
    @rule(+(~~x::hasrepeats) => +(merge_repeats(*, ~~x)...))
    
    @acrule((~z::_iszero + ~x) => ~x)
    @rule(+(~x) => ~x)
]

const TIMES_RULES2 = [
    @rule(*(~~x::isnotflat(*)) => flatten_term(*, ~~x))
    @rule(*(~~x::!(issortedₑ)) => sort_args(*, ~~x))
    
    @acrule(~a::isnumber * ~b::isnumber => ~a * ~b)
    @rule(*(~~x::hasrepeats) => *(merge_repeats(^, ~~x)...))
    
    @acrule((~y)^(~n) * ~y => (~y)^(~n+1))
    @acrule((~x)^(~n) * (~x)^(~m) => (~x)^(~n + ~m))

    @acrule((~z::_isone  * ~x) => ~x)
    @acrule((~z::_iszero *  ~x) => ~z)
    @rule(*(~x) => ~x)
]


const POW_RULES2 = [
    @rule(^(*(~~x), ~y::isliteral(Integer)) => *(map(a->pow(a, ~y), ~~x)...))
    @rule((((~x)^(~p::isliteral(Integer)))^(~q::isliteral(Integer))) => (~x)^((~p)*(~q)))
    @rule(^(~x, ~z::_iszero) => 1)
    @rule(^(~x, ~z::_isone) => ~x)
]

const ASSORTED_RULES2 = [
    @rule(identity(~x) => ~x)
    @rule(-(~x) => -1*~x)
    @rule(-(~x, ~y) => ~x + -1(~y))
    @rule(~x / ~y => ~x * pow(~y, -1))
    @rule(one(~x) => one(symtype(~x)))
    @rule(zero(~x) => zero(symtype(~x)))
    @rule(cond(~x::isnumber, ~y, ~z) => ~x ? ~y : ~z)
]

const TRIG_RULES2 = [
    @acrule(sin(~x)^2 + cos(~x)^2 => one(~x))
    @acrule(sin(~x)^2 + -1        => cos(~x)^2)
    @acrule(cos(~x)^2 + -1        => sin(~x)^2)

    @acrule(tan(~x)^2 + -1*sec(~x)^2 => one(~x))
    @acrule(tan(~x)^2 +  1 => sec(~x)^2)
    @acrule(sec(~x)^2 + -1 => tan(~x)^2)

    @acrule(cot(~x)^2 + -1*csc(~x)^2 => one(~x))
    @acrule(cot(~x)^2 +  1 => csc(~x)^2)
    @acrule(csc(~x)^2 + -1 => cot(~x)^2)
]

const BOOLEAN_RULES2 = [
    @rule((true | (~x)) => true)
    @rule(((~x) | true) => true)
    @rule((false | (~x)) => ~x)
    @rule(((~x) | false) => ~x)
    @rule((true & (~x)) => ~x)
    @rule(((~x) & true) => ~x)
    @rule((false & (~x)) => false)
    @rule(((~x) & false) => false)

    @rule(!(~x) & ~x => false)
    @rule(~x & !(~x) => false)
    @rule(!(~x) | ~x => true)
    @rule(~x | !(~x) => true)
    @rule(xor(~x, !(~x)) => true)
    @rule(xor(~x, ~x) => false)

    @rule(~x == ~x => true)
    @rule(~x != ~x => false)
    @rule(~x < ~x => false)
    @rule(~x > ~x => false)

    # simplify terms with no symbolic arguments
    # e.g. this simplifies term(isodd, 3, type=Bool)
    # or term(!, false)
    @rule((~f)(~x::isnumber) => (~f)(~x))
    # and this simplifies any binary comparison operator
    @rule((~f)(~x::isnumber, ~y::isnumber) => (~f)(~x, ~y))
]

NEW_RULES = [
    @rule(identity(~x) => ~x)
    @rule(-(~x) => -1*~x)
    @rule(-(~x, ~y) => ~x + -1(~y))
    @rule(~x / ~y => ~x * pow(~y, -1))
    @rule(one(~x) => one(symtype(~x)))
    @rule(zero(~x) => zero(symtype(~x)))

    @rule(cond(~x::(x->x isa Bool), ~y, ~z) => ~x ? ~y : ~z)
    #@rule(*(~~x, *(~~y), ~~z) => *((~~x)..., (~~y)..., (~~z)...)),
    @rule(*(~~x::isnotflat(*)) => flatten_term(*, ~~x))
    @rule(*(~~x::!(issortedₑ)) => sort_args(*, ~~x))
    @rule(*(~a::isnumber, ~b::isnumber, ~~x) => *(~a * ~b, (~~x)...))

    #@rule(+(~~x, +(~~y), ~~z) => +((~~x)..., (~~y)..., (~~z)...)),
    @rule(+(~~x::isnotflat(+)) => flatten_term(+, ~~x))
    @rule(+(~~x::!(issortedₑ)) => sort_args(+, ~~x))
    @rule(+(~a::isnumber, ~b::isnumber, ~~x) => +((~~x)..., ~a + ~b))

    @acrule(*(~~x) + *(~β, ~~x) => *(1 + ~β, (~~x)...))
    @acrule(*(~α, ~~x) + *(~β, ~~x) => *(~α + ~β, (~~x)...))
    @acrule(*(~~x, ~α) + *(~~x, ~β) => *(~α + ~β, (~~x)...))

    @acrule(~x + *(~β, ~x) => *(1 + ~β, ~x))
    @acrule(*(~α::isnumber, ~x) + ~x => *(~α + 1, ~x))

    @acrule((~z::_iszero + ~x) => ~x)
    @rule(+(~x) => ~x)

    @rule(*(~~x::hasrepeats) => *(merge_repeats(^, ~~x)...))
    @rule(+(~~x::hasrepeats) => +(merge_repeats(*, ~~x)...))

    @acrule((~y)^(~n) * ~y => (~y)^(~n+1))
    @acrule((~x)^(~n) * (~x)^(~m) => (~x)^(~n + ~m))

    @acrule((~z::_isone  * ~x) => ~x)
    @acrule((~z::_iszero *  ~x) => ~z)
    @rule(*(~x) => ~x)

    @rule(^(*(~~x), ~y::isliteral(Integer)) => *(map(a->pow(a, ~y), ~~x)...))
    @rule((((~x)^(~p::isliteral(Integer)))^(~q::isliteral(Integer))) => (~x)^((~p)*(~q)))
    @rule(^(~x, ~z::_iszero) => 1)
    @rule(^(~x, ~z::_isone) => ~x)
]

OLD_BASIC_NUMBER_RULES2 = let # Keep these around for benchmarking purposes
    [
     @rule(~x - ~y => ~x + (-1 * ~y)),
     @rule(~x / ~y => ~x * pow(~y, -1)),
     #@rule(*(~~x, *(~~y), ~~z) => *((~~x)..., (~~y)..., (~~z)...)),
     @rule(*(~~x::isnotflat(*)) => flatten_term(*, ~~x)),
     @rule(*(~~x::!(issortedₑ)) => sort_args(*, ~~x)),
     @rule(*(~a::isnumber, ~b::isnumber, ~~x) => *(~a * ~b, (~~x)...)),

     #@rule(+(~~x, +(~~y), ~~z) => +((~~x)..., (~~y)..., (~~z)...)),
     @rule(+(~~x::isnotflat(+)) => flatten_term(+, ~~x)),
     @rule(+(~~x::!(issortedₑ)) => sort_args(+, ~~x)),
     @rule(+(~a::isnumber, ~b::isnumber, ~~x) => +((~~x)..., ~a + ~b)),

     @rule(+(~~a, *(~~x), *(~β::isnumber, ~~x), ~~b) =>
           +((~~a)..., *(1 + ~β, (~x)...), (~b)...)),
     @rule(+(~~a, *(~α::isnumber, ~x), ~~b, ~x, ~~c) =>
           +((~~a)..., *(+(~α+1), ~x), (~~b)..., (~~c)...)),
     @rule(+(~~a, *(~α::isnumber, ~~x), *(~β::isnumber, ~~x), ~~b) =>
           +((~~a)..., *(~α + ~β, (~x)...), (~b)...)),

     # group stuff
     @rule(^(*(~~x), ~y) => *(map(a->a ^ (~y), ~~x)...)),
     @rule(*(~~x, ^(~y, ~n), ~y, ~~z) => *((~~x)..., ^(~y, ~n+1), (~~z)...)),
     @rule(*(~~a, ^(~x, ~e1), ^(~x, ~e2), ~~b) =>
           *((~~a)..., ^(~x, (~e1 + ~e2)), (~b)...)),
     @rule((((~x)^(~p))^(~q)) => (~x)^((~p)*(~q))),
     @rule(+(~~x::hasrepeats) => +(merge_repeats(*, ~~x)...)),
     @rule(*(~~x::hasrepeats) => *(merge_repeats(^, ~~x)...)),

     @rule(*(~z::_iszero, ~~x) => ~z),

     # remove the idenitities
     @rule(*(~z::_isone, ~~x::(!isempty)) => *((~~x)...)),
     @rule(+(~z::_iszero, ~~x::(!isempty)) => +((~~x)...)),
     @rule(^(~x, ~z::_iszero) => 1),
     @rule(^(~x, ~z::_isone) => ~x),
     ]
end
