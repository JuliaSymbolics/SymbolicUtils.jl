using .Rewriters

let
    PLUS_RULES = [
        @rule(~x::isnotflat(+) => flatten_term(+, ~x))
        @rule(~x::needs_sorting(+) => sort_args(+, ~x))
        @ordered_acrule(~a::is_literal_number + ~b::is_literal_number => ~a + ~b)

        @acrule(*(~~x) + *(~β, ~~x) => *(1 + ~β, (~~x)...))
        @acrule(*(~α, ~~x) + *(~β, ~~x) => *(~α + ~β, (~~x)...))
        @acrule(*(~~x, ~α) + *(~~x, ~β) => *(~α + ~β, (~~x)...))

        @acrule(~x + *(~β, ~x) => *(1 + ~β, ~x))
        @acrule(*(~α::is_literal_number, ~x) + ~x => *(~α + 1, ~x))
        @rule(+(~~x::hasrepeats) => +(merge_repeats(*, ~~x)...))

        @ordered_acrule((~z::_iszero + ~x) => ~x)
        @rule(+(~x) => ~x)
    ]

    TIMES_RULES = [
        @rule(~x::isnotflat(*) => flatten_term(*, ~x))
        @rule(~x::needs_sorting(*) => sort_args(*, ~x))

        @ordered_acrule(~a::is_literal_number * ~b::is_literal_number => ~a * ~b)
        @rule(*(~~x::hasrepeats) => *(merge_repeats(^, ~~x)...))

        @acrule((~y)^(~n) * ~y => (~y)^(~n+1))
        @ordered_acrule((~x)^(~n) * (~x)^(~m) => (~x)^(~n + ~m))

        @ordered_acrule((~z::_isone  * ~x) => ~x)
        @ordered_acrule((~z::_iszero *  ~x) => ~z)
        @rule(*(~x) => ~x)
    ]

    POW_RULES = [
        @rule(^(*(~~x), ~y::_isinteger) => *(map(a->pow(a, ~y), ~~x)...))
        @rule((((~x)^(~p::_isinteger))^(~q::_isinteger)) => (~x)^((~p)*(~q)))
        @rule(^(~x, ~z::_iszero) => 1)
        @rule(^(~x, ~z::_isone) => ~x)
        @rule(inv(~x) => 1/(~x))
    ]

    ASSORTED_RULES = [
        @rule(identity(~x) => ~x)
        @rule(-(~x) => -1*~x)
        @rule(-(~x, ~y) => ~x + -1(~y))
        @rule(~x::_isone \ ~y => ~y)
        @rule(~x \ ~y => ~y / (~x))
        @rule(one(~x) => one(symtype(~x)))
        @rule(zero(~x) => zero(symtype(~x)))
        @rule(conj(~x::_isreal) => ~x)
        @rule(real(~x::_isreal) => ~x)
        @rule(imag(~x::_isreal) => zero(symtype(~x)))
        @rule(ifelse(~x::is_literal_number, ~y, ~z) => ~x ? ~y : ~z)
    ]

    TRIG_EXP_RULES = [
        @acrule(~r*~x::has_trig_exp + ~r*~y => ~r*(~x + ~y))
        @acrule(~r*~x::has_trig_exp + -1*~r*~y => ~r*(~x - ~y))
        @acrule(sin(~x)^2 + cos(~x)^2 => one(~x))
        @acrule(sin(~x)^2 + -1        => cos(~x)^2)
        @acrule(cos(~x)^2 + -1        => sin(~x)^2)

        @acrule(cos(~x)^2 + -1*sin(~x)^2 => cos(2 * ~x))
        @acrule(cos(~x)^2 + -1*sin(~x)^2 => cos(2 * ~x))
        @acrule(cos(~x) * sin(~x) => sin(2 * ~x)/2)

        @acrule(tan(~x)^2 + -1*sec(~x)^2 => one(~x))
        @acrule(tan(~x)^2 +  1 => sec(~x)^2)
        @acrule(sec(~x)^2 + -1 => tan(~x)^2)

        @acrule(cot(~x)^2 + -1*csc(~x)^2 => one(~x))
        @acrule(cot(~x)^2 +  1 => csc(~x)^2)
        @acrule(csc(~x)^2 + -1 => cot(~x)^2)

        @acrule(exp(~x) * exp(~y) => _iszero(~x + ~y) ? 1 : exp(~x + ~y))
        @rule(exp(~x)^(~y) => exp(~x * ~y))
    ]

    DIVREMMOD_RULES = [
        @rule(mod(~x::_isinteger, ~m::(m -> _isone(m) || _isone(-m))) => 0)
        @rule(mod((~n::_isinteger) * (~~xs::_areintegers), ~m::_isnonzerointeger) => mod(~n * prod(~~xs) - ~m * div(~n, ~m) * prod(~~xs), ~m))
        @rule(mod(+(~~xs::_areintegers), ~m::_isnonzerointeger) => mod(sum(~~xs) - sum(x -> x isa Mul && first(arguments(x)) isa Number ? let (n, rs...) = arguments(x); ~m * div(n, ~m) * prod(rs) end : 0, ~~xs), ~m))

        @rule(rem(~x::_isinteger, ~m::(m -> _isone(m) || _isone(-m))) => 0)
        @rule(rem((~n::_isinteger) * (~~xs::_areintegers), ~m::_isnonzerointeger) => rem(~n * prod(~~xs) - ~m * div(~n, ~m) * prod(~~xs), ~m))
        @rule(rem(+(~~xs::_areintegers), ~m::_isnonzerointeger) => rem(sum(~~xs) - sum(x -> x isa Mul && first(arguments(x)) isa Number ? let (n, rs...) = arguments(x); ~m * div(n, ~m) * prod(rs) end : 0, ~~xs), ~m))

        @rule(div(~x::_isinteger, ~m::(m -> _isone(m) || _isone(-m))) => ~m * ~x)
        @rule(div((~n::_isinteger) * (~~xs::_areintegers), ~m::_isnonzerointeger) => div(~n, ~m) * prod(~~xs) + div(~n * prod(~~xs) - ~m * div(~n, ~m) * prod(~~xs), ~m))
        @rule(div(+(~~xs::_areintegers), ~m::_isnonzerointeger) => sum(x -> x isa Mul && first(arguments(x)) isa Number ? let (n, rs...) = arguments(x); div(n, ~m) * prod(rs) end : 0, ~~xs) + div(sum(~~xs) - sum(x -> x isa Mul && first(arguments(x)) isa Number ? let (n, rs...) = arguments(x); ~m * div(n, ~m) * prod(rs) end : 0, ~~xs), ~m))

        @acrule(div(~x::_isreal, ~m::_isone) + rem(~x::_isreal, ~m) => ~x)
        @acrule(~m::(m -> m isa Number && !iszero(m)) * div(~x::_isreal, ~m) + rem(~x::_isreal, ~m) => ~x)
    ]

    BOOLEAN_RULES = [
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
        @rule((~f)(~x::is_literal_number) => (~f)(~x))
        # and this simplifies any binary comparison operator
        @rule((~f)(~x::is_literal_number, ~y::is_literal_number) => (~f)(~x, ~y))
    ]

    function number_simplifier()
        rule_tree = [If(istree, Chain(ASSORTED_RULES)),
                     If(is_operation(+),
                        Chain(PLUS_RULES)),
                     If(is_operation(*),
                        Chain(TIMES_RULES)),
                     If(is_operation(^),
                        Chain(POW_RULES))] |> RestartedChain

        rule_tree
    end

    trig_exp_simplifier(;kw...) = Chain(TRIG_EXP_RULES)

    divremmod_simplifier() = Chain(DIVREMMOD_RULES)

    bool_simplifier() = Chain(BOOLEAN_RULES)

    global default_simplifier
    global serial_simplifier
    global threaded_simplifier
    global serial_simplifier
    global serial_expand_simplifier

    function default_simplifier(; kw...)
        IfElse(t -> (has_trig_exp(t) || has_div_rem_mod(t)),
               Postwalk(IfElse(x->symtype(x) <: Number,
                               Chain((number_simplifier(),
                                      trig_exp_simplifier(),
                                      divremmod_simplifier())),
                               If(x->symtype(x) <: Bool,
                                  bool_simplifier()))
                        ; kw...),
               Postwalk(Chain((If(x->symtype(x) <: Number,
                                  number_simplifier()),
                               If(x->symtype(x) <: Bool,
                                  bool_simplifier())))
                        ; kw...))
    end

    # reduce overhead of simplify by defining these as constant
    serial_simplifier = If(istree, Fixpoint(default_simplifier()))

    threaded_simplifier(cutoff) = Fixpoint(default_simplifier(threaded=true,
                                                              thread_cutoff=cutoff))

    serial_expand_simplifier = If(istree,
                                  Fixpoint(Chain((expand,
                                                  Fixpoint(default_simplifier())))))

end
