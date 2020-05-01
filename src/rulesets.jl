
const SIMPLIFY_RULES = RuleSet([
    @rule ~t::sym_isa(Number) => NUMBER_RULES(~t, applyall=true, recurse=true)
])

const NUMBER_RULES = RuleSet([
    @rule ~t               => ASSORTED_RULES(~t, recurse=false)
    @rule ~t::is_operation(+) =>  PLUS_RULES(~t, recurse=false)
    @rule ~t::is_operation(*) => TIMES_RULES(~t, recurse=false)
    @rule ~t::is_operation(^) =>   POW_RULES(~t, recurse=false)
    @rule ~t                  =>  TRIG_RULES(~t, recurse=false)
])

const PLUS_RULES = RuleSet([
    @rule(+(~~x::isnotflat(+)) => flatten_term(+, ~~x))
    @rule(+(~~x::!(issortedₑ)) => sort_args(+, ~~x))
    @acrule(~a::isnumber + ~b::isnumber => ~a + ~b)

    @acrule(*(~~x) + *(~β, ~~x) => *(1 + ~β, (~~x)...))
    @acrule(*(~α, ~~x) + *(~β, ~~x) => *(~α +  ~β, (~~x)...))
    @acrule(*(~~x, ~α) + *(~~x, ~β,) => *(~α +  ~β, (~~x)...))

    @acrule(~x + *(~β, ~x) => *(1 + ~β, ~x))
    @acrule(*(~α::isnumber, ~x) + ~x => *(~α + 1, ~x))
    @rule(+(~~x::hasrepeats) => +(merge_repeats(*, ~~x)...))
    
    @acrule((~z::_iszero + ~x) => ~x)
    @rule(+(~x) => ~x)
])

const TIMES_RULES = RuleSet([
    @rule(*(~~x::isnotflat(*)) => flatten_term(*, ~~x))
    @rule(*(~~x::!(issortedₑ)) => sort_args(*, ~~x))
    
    @acrule(~a::isnumber * ~b::isnumber => ~a * ~b)
    @rule(*(~~x::hasrepeats) => *(merge_repeats(^, ~~x)...))
    
    @acrule((~y)^(~n) * ~y => (~y)^(~n+1))
    @acrule((~x)^(~n) * (~x)^(~m) => (~x)^(~n + ~m))

    @acrule((~z::_isone  * ~x) => ~x)
    @acrule((~z::_iszero *  ~x) => ~z)
    @rule(*(~x) => ~x)
])

const POW_RULES = RuleSet([
    @rule(^(*(~~x), ~y) => *(map(a->pow(a, ~y), ~~x)...))
    @rule((((~x)^(~p))^(~q)) => (~x)^((~p)*(~q)))
    @rule(^(~x, ~z::_iszero) => 1)
    @rule(^(~x, ~z::_isone) => ~x)
])

const ASSORTED_RULES = RuleSet([
    @rule(identity(~x) => ~x)
    @rule(-(~x, ~y) => ~x + -1(~y))
    @rule(~x / ~y => ~x * pow(~y, -1))
])

const TRIG_RULES = RuleSet([
    @acrule(sin(~x)^2 + cos(~x)^2 => one(~x))
    @acrule(sin(~x)^2 + -1        => cos(~x)^2)
    @acrule(cos(~x)^2 + -1        => sin(~x)^2)

    @acrule(tan(~x)^2 + -1*sec(~x)^2 => one(~x))
    @acrule(tan(~x)^2 +  1 => sec(~x)^2)
    @acrule(sec(~x)^2 + -1 => tan(~x)^2)

    @acrule(cot(~x)^2 + -1*csc(~x)^2 => one(~x))
    @acrule(cot(~x)^2 +  1 => csc(~x)^2)
    @acrule(csc(~x)^2 + -1 => cot(~x)^2)
])



OLD_BASIC_NUMBER_RULES = let # Keep these around for benchmarking purposes
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
