module Rewriters
using SymbolicUtils: @timer, is_operation, istree, symtype, Term, operation, arguments,
                     node_count

export Empty, IfElse, If, Chain, RestartedChain, Fixpoint, Postwalk, Prewalk, PassThrough

struct Empty end

(ctx::Empty)(x) = x

struct IfElse{F, A, B}
    cond::F
    yes::A
    no::B
end

function (ctx::IfElse)(x)
    ctx.cond(x) ?  ctx.yes(x) : ctx.no(x)
end

If(f, x) = IfElse(f, x, Empty())

struct Chain{Cs}
    ctxs::Cs
end

function (ctx::Chain)(x)
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
            return Chain(ctx.ctxs)(y)
        end
    end
    return x
end

struct Fixpoint{C}
    ctx::C
end

const rule_repr = IdDict()

function (ctx::Fixpoint)(x)
    f = ctx.ctx
    y = @timer Base.@get!(rule_repr, f, repr(f)) f(x)
    while x !== y && !isequal(x, y)
        isnothing(y) && return x
        x = y
        y = @timer Base.@get!(rule_repr, f, repr(f)) f(x)
    end
    return x
end

struct Walk{ord, C, threaded}
    ctx::C
    thread_cutoff::Int
end

using .Threads

function Postwalk(ctx; threaded::Bool=false, thread_cutoff=100)
    Walk{:post, typeof(ctx), threaded}(ctx, thread_cutoff)
end

function Prewalk(ctx; threaded::Bool=false, thread_cutoff=100)
    Walk{:pre, typeof(ctx), threaded}(ctx, thread_cutoff)
end

struct PassThrough{C}
    ctx::C
end
(p::PassThrough)(x) = (y=p.ctx(x); isnothing(y) ? x : y)

passthrough(x, default) = isnothing(x) ? default : x
function (p::Walk{ord, C, false})(x) where {ord, C}
    if istree(x)
        if ord === :pre
            x = p.ctx(x)
        end
        if istree(x)
            x = Term{symtype(x)}(operation(x),
                                 map(t->PassThrough(p)(t),
                                     arguments(x)))
        end
        return ord === :post ? p.ctx(x) : x
    else
        return p.ctx(x)
    end
end

function (p::Walk{ord, C, true})(x) where {ord, C}
    if istree(x)
        if ord === :pre
            x = p.ctx(x)
        end
        if istree(x)
            _args = map(arguments(x)) do arg
                if node_count(arg) > p.thread_cutoff
                    Threads.@spawn p(arg)
                else
                    p(arg)
                end
            end
            args = map((t,a) -> passthrough(t isa Task ? fetch(t) : t, a), _args, arguments(x))
            t = Term{symtype(x)}(operation(x), args)
        end
        return ord === :post ? p.ctx(t) : t
    else
        return p.ctx(x)
    end
end

end # end module

using .Rewriters

let
    NUMBER_RULES2 = [
        @rule ~t               => ASSORTED_RULES2(~t)
        @rule ~t::is_operation(+) =>  PLUS_RULES2(~t)
        @rule ~t::is_operation(*) => TIMES_RULES2(~t)
        @rule ~t::is_operation(^) =>   POW_RULES2(~t)
    ]

    PLUS_RULES2 = [
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

    TIMES_RULES2 = [
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


    POW_RULES2 = [
        @rule(^(*(~~x), ~y::isliteral(Integer)) => *(map(a->pow(a, ~y), ~~x)...))
        @rule((((~x)^(~p::isliteral(Integer)))^(~q::isliteral(Integer))) => (~x)^((~p)*(~q)))
        @rule(^(~x, ~z::_iszero) => 1)
        @rule(^(~x, ~z::_isone) => ~x)
    ]

    ASSORTED_RULES2 = [
        @rule(identity(~x) => ~x)
        @rule(-(~x) => -1*~x)
        @rule(-(~x, ~y) => ~x + -1(~y))
        @rule(~x / ~y => ~x * pow(~y, -1))
        @rule(one(~x) => one(symtype(~x)))
        @rule(zero(~x) => zero(symtype(~x)))
        @rule(cond(~x::isnumber, ~y, ~z) => ~x ? ~y : ~z)
    ]

    TRIG_RULES2 = [
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

    BOOLEAN_RULES2 = [
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


    bool_simplifier() = Chain(BOOLEAN_RULES2)

    function number_simplifier()
        rule_tree = [Chain(ASSORTED_RULES2),
                     If(is_operation(+),
                        Chain(PLUS_RULES2)),
                     If(is_operation(*),
                        Chain(TIMES_RULES2)),
                     If(is_operation(^),
                        Chain(POW_RULES2))] |> RestartedChain

        rule_tree
    end
    trig_simplifier(;kw...) = Chain(TRIG_RULES2)

    # TODO: make Fixpoint efficient and use it for each.
    function default_simplifier(; kw...)
        IfElse(has_trig,
               Postwalk(Chain((If(x->symtype(x) <: Number, number_simplifier()),
                               trig_simplifier(),
                               If(x->symtype(x) <: Bool, bool_simplifier()))); kw...),
               Postwalk(Chain((If(x->symtype(x) <: Number, number_simplifier()),
                               If(x->symtype(x) <: Bool, bool_simplifier()))); kw...))
    end

    polynorm_rewriter() = x->to_term(to_mpoly(x)...)

    global simplify

    function simplify(x;
                       polynorm=false,
                       threaded=false,
                       thread_subtree_cutoff=100)

        default = default_simplifier(threaded=threaded,
                                     thread_cutoff=thread_subtree_cutoff)
        if polynorm
            Fixpoint(Chain((polynorm_rewriter(),
                            Fixpoint(default))))(x)
        else
            Fixpoint(default)(x)
        end
    end
end
