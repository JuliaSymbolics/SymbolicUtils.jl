using .Rewriters
"""
  is_operation(f)
Returns a single argument anonymous function predicate, that returns `true` if and only if
the argument to the predicate satisfies `iscall` and `operation(x) == f`
"""
is_operation(f) = @nospecialize(x) -> iscall(x) && (operation(x) === f)

const CANONICALIZE_PLUS = (
    @rule(~x::isnotflat(+) => flatten_term(+, ~x)),
    @rule(~x::needs_sorting(+) => sort_args(+, ~x)),
    @ordered_acrule(~a::is_literal_number + ~b::is_literal_number => ~a + ~b),

    @acrule(*(~~x) + *(~β, ~~x) => *(1 + ~β, (~~x)...)),

    @acrule(~x + *(~β, ~x) => *(1 + ~β, ~x)),
    @acrule(*(~α::is_literal_number, ~x) + ~x => *(~α + 1, ~x)),
    @rule(+(~~x::hasrepeats) => +(merge_repeats(*, ~~x)...)),

    @ordered_acrule((~z::_iszero + ~x) => ~x),
    @rule(+(~x) => ~x),
)

const PLUS_DISTRIBUTE = (
    @acrule(*(~α, ~~x) + *(~β, ~~x) => *(~α + ~β, (~~x)...)),
    @acrule(*(~~x, ~α) + *(~~x, ~β) => *(~α + ~β, (~~x)...)),
)

const CANONICALIZE_TIMES = (
    @rule(~x::isnotflat(*) => flatten_term(*, ~x)),
    @rule(~x::needs_sorting(*) => sort_args(*, ~x)),

    @ordered_acrule(~a::is_literal_number * ~b::is_literal_number => ~a * ~b),
    @rule(*(~~x::hasrepeats) => *(merge_repeats(^, ~~x)...)),

    @acrule((~y)^(~n) * ~y => (~y)^(~n+1)),

    @ordered_acrule((~z::_isone  * ~x) => ~x),
    @ordered_acrule((~z::_iszero *  ~x) => ~z),
    @rule(*(~x) => ~x),
)

const MUL_DISTRIBUTE = Chain((
    @ordered_acrule((~x)^(~n) * (~x)^(~m) => (~x)^(~n + ~m)),
    @acrule((~y)^(~n) * ~y => (~y)^(~n + 1)),
))

const CANONICALIZE_POW = (
    @rule(^(*(~~x), ~y::_isinteger) => *(map(a->pow(a, ~y), ~~x)...)),
    @rule((((~x)^(~p::_isinteger))^(~q::_isinteger)) => (~x)^((~p)*(~q))),
    @rule(^(~x, ~z::_iszero) => 1),
    @rule(^(~x, ~z::_isone) => ~x),
    @rule(inv(~x) => 1/(~x)),
)

const POW_RULES = (
    @rule(^(~x::_isone, ~z) => 1),
    @rule(ℯ^(~x) => exp(~x)),
    @rule((~x)^(1//2) => sqrt(~x)),
    @rule(sqrt((~x)^2) => abs(~x)),
)

const ASSORTED_RULES = (
    @rule(sqrt(~x::is_literal_number) => _extract_perfect_square(~x)),
    @rule(identity(~x) => ~x),
    @rule(-(~x) => -1*~x),
    @rule(-(~x, ~y) => ~x + -1(~y)),
    @rule(~x::_isone \ ~y => ~y),
    @rule(~x \ ~y => ~y / (~x)),
    @rule(one(~x) => one(symtype(~x))),
    @rule(zero(~x) => zero(symtype(~x))),
    @rule(conj(~x::_isreal) => ~x),
    @rule(real(~x::_isreal) => ~x),
    @rule(imag(~x::_isreal) => zero(symtype(~x))),
    # log∘exp is identity on reals; complex branch cuts differ by 2πi
    @rule(log(exp(~x::_isreal)) => ~x),
    # exp∘log is identity wherever log is defined
    @rule(exp(log(~x)) => ~x),
    @rule(ifelse(~x::is_literal_number, ~y, ~z) => ~x ? ~y : ~z),
    @rule(ifelse(~x, ~y, ~y) => ~y),
    @rule(ifelse_eager(~x::is_literal_number, ~y, ~z) => ~x ? ~y : ~z),
    @rule(ifelse_eager(~x, ~y, ~y) => ~y),
    @rule(ifelse_branching(~x::is_literal_number, ~y, ~z) => ~x ? ~y : ~z),
    @rule(ifelse_branching(~x, ~y, ~y) => ~y),
)

const TRIG_EXP_RULES = (
    @acrule(~r*~x::has_trig_exp + ~r*~y => ~r*(~x + ~y)),
    @acrule(~r*~x::has_trig_exp + -1*~r*~y => ~r*(~x - ~y)),
    @acrule(sin(~x)^2 + cos(~x)^2 => one(~x)),
    # Direct scaled form: Mul(-1, Add(...)) distributes -1 into the Add, so the
    # factoring rule above cannot reduce -sin^2 - cos^2 via r*(sin^2+cos^2).
    @acrule(~r*sin(~x)^2 + ~r*cos(~x)^2 => ~r),
    @acrule(sin(~x)^2 + -1        => -1*cos(~x)^2),
    @acrule(cos(~x)^2 + -1        => -1*sin(~x)^2),

    @acrule(cos(~x)^2 + -1*sin(~x)^2 => cos(2 * ~x)),
    @acrule(sin(~x)^2 + -1*cos(~x)^2 => -cos(2 * ~x)),
    @acrule(cos(~x) * sin(~x) => sin(2 * ~x)/2),

    @acrule(tan(~x)^2 + -1*sec(~x)^2 => one(~x)),
    @acrule(-1*tan(~x)^2 + sec(~x)^2 => one(~x)),
    @acrule(tan(~x)^2 +  1 => sec(~x)^2),
    @acrule(sec(~x)^2 + -1 => tan(~x)^2),

    @acrule(cot(~x)^2 + -1*csc(~x)^2 => one(~x)),
    @acrule(cot(~x)^2 +  1 => csc(~x)^2),
    @acrule(csc(~x)^2 + -1 => cot(~x)^2),

    @acrule(cosh(~x)^2 + -1*sinh(~x)^2 => one(~x)),
    @acrule(cosh(~x)^2 + -1            => sinh(~x)^2),
    @acrule(sinh(~x)^2 +  1            => cosh(~x)^2),

    @acrule(cosh(~x)^2 + sinh(~x)^2 => cosh(2 * ~x)),
    @acrule(cosh(~x) * sinh(~x) => sinh(2 * ~x)/2),

    @acrule(exp(~x) * exp(~y) => _iszero(~x + ~y) ? 1 : exp(~x + ~y)),
    @rule(exp(~x)^(~y) => exp(~x * ~y)),
)

const BOOLEAN_RULES = (
    @rule((true | (~x)) => true),
    @rule(((~x) | true) => true),
    @rule((false | (~x)) => ~x),
    @rule(((~x) | false) => ~x),
    @rule((true & (~x)) => ~x),
    @rule(((~x) & true) => ~x),
    @rule((false & (~x)) => false),
    @rule(((~x) & false) => false),

    @rule(!(~x) & ~x => false),
    @rule(~x & !(~x) => false),
    @rule(!(~x) | ~x => true),
    @rule(~x | !(~x) => true),
    @rule(xor(~x, !(~x)) => true),
    @rule(xor(~x, ~x) => false),

    @rule(~x == ~x => true),
    @rule(~x != ~x => false),
    @rule(~x < ~x => false),
    @rule(~x > ~x => false),

    # simplify terms with no symbolic arguments
    # e.g. this simplifies term(isodd, 3, type=Bool)
    # or term(!, false)
    @rule((~f)(~x::is_literal_number) => (~f)(~x)),
    # and this simplifies any binary comparison operator
    @rule((~f)(~x::is_literal_number, ~y::is_literal_number) => (~f)(~x, ~y)),
)

const NUMBER_SIMPLIFIER = RestartedChain((
    If(iscall, Chain(ASSORTED_RULES)),
    If(x -> !isadd(x) && is_operation(+)(x),
    Chain(CANONICALIZE_PLUS)),
    If(is_operation(+), Chain(PLUS_DISTRIBUTE)), # This would be useful even if isadd
    If(x -> !ismul(x) && is_operation(*)(x),
    Chain(CANONICALIZE_TIMES)),
    If(is_operation(*), MUL_DISTRIBUTE),
    If(x -> !ispow(x) && is_operation(^)(x),
    Chain(CANONICALIZE_POW)),
    If(is_operation(^), Chain(POW_RULES)),
))

const TRIG_EXP_SIMPLIFIER = Chain(TRIG_EXP_RULES)

# --- Trig reduce: product-to-sum and power reduction (opt-in) ---

"""
    _trig_power_reduce(f, x, n)

Reduce `f(x)^n` (where `f` is `sin`, `cos`, `sinh`, or `cosh` and `n ≥ 2`) by
one step using the half-angle / double-argument identities:

    cos(x)^2  = (1 + cos(2x)) / 2
    sin(x)^2  = (1 - cos(2x)) / 2
    cosh(x)^2 = (1 + cosh(2x)) / 2
    sinh(x)^2 = (cosh(2x) - 1) / 2

For `n ≥ 3` the result `f(x)^r * half_angle^k` still contains powers and will
be reduced further by subsequent Fixpoint iterations.
"""
function _trig_power_reduce(f, x, n)
    k = div(n, 2)   # number of squared pairs
    r = rem(n, 2)   # leftover power (0 or 1)
    if f === cos
        sq = (1 + cos(2 * x)) / 2
    elseif f === sin
        sq = (1 - cos(2 * x)) / 2
    elseif f === cosh
        sq = (1 + cosh(2 * x)) / 2
    elseif f === sinh
        sq = (cosh(2 * x) - 1) / 2
    else
        return nothing
    end
    return f(x)^r * sq^k
end

_isinteger_ge2(n) = n isa Integer && n >= 2

"""
    _has_neg_leading(x)

Return `true` if `x` "looks negative": a negative number, a Mul with a negative
numeric first argument, or an Add whose first sorted term looks negative.
Used to canonicalise `cos(-expr) → cos(expr)` and `sin(-expr) → -sin(expr)`.
"""
function _has_neg_leading(x)
    x = unwrap_const(x)
    x isa Number && return x < 0
    !iscall(x) && return false
    if ismul(x)
        a = unwrap_const(first(arguments(x)))
        return a isa Number && a < 0
    end
    if isadd(x)
        a = first(sorted_arguments(x))
        return _has_neg_leading(a)
    end
    return false
end

const TRIG_REDUCE_RULES = (
    # ── Cleanup: fold literal values, normalize negative arguments ──
    @rule(sin(~x::_iszero) => 0),
    @rule(cos(~x::_iszero) => 1),
    @rule(sinh(~x::_iszero) => 0),
    @rule(cosh(~x::_iszero) => 1),
    @rule(cos(~x::_has_neg_leading) => cos(-1 * ~x)),      # cos is even
    @rule(sin(~x::_has_neg_leading) => -1 * sin(-1 * ~x)), # sin is odd
    @rule(cosh(~x::_has_neg_leading) => cosh(-1 * ~x)),    # cosh is even
    @rule(sinh(~x::_has_neg_leading) => -1 * sinh(-1 * ~x)), # sinh is odd

    # ── Power reduction: f(x)^n for n ≥ 2 ──
    # Circular
    @rule(cos(~x)^(~n::_isinteger_ge2) => _trig_power_reduce(cos, ~x, ~n)),
    @rule(sin(~x)^(~n::_isinteger_ge2) => _trig_power_reduce(sin, ~x, ~n)),
    # Hyperbolic
    @rule(cosh(~x)^(~n::_isinteger_ge2) => _trig_power_reduce(cosh, ~x, ~n)),
    @rule(sinh(~x)^(~n::_isinteger_ge2) => _trig_power_reduce(sinh, ~x, ~n)),
    # tan/sec: tan(x)^2 → sec(x)^2 - 1
    @rule(tan(~x)^2 => sec(~x)^2 - 1),
    @rule(cot(~x)^2 => csc(~x)^2 - 1),

    # ── Product-to-sum (linearization): circular ──
    @acrule(cos(~x) * cos(~y) => (cos(~x - ~y) + cos(~x + ~y)) / 2),
    @acrule(sin(~x) * sin(~y) => (cos(~x - ~y) - cos(~x + ~y)) / 2),
    @acrule(sin(~x) * cos(~y) => (sin(~x + ~y) + sin(~x - ~y)) / 2),

    # ── Product-to-sum (linearization): hyperbolic ──
    @acrule(cosh(~x) * cosh(~y) => (cosh(~x - ~y) + cosh(~x + ~y)) / 2),
    @acrule(sinh(~x) * sinh(~y) => (cosh(~x + ~y) - cosh(~x - ~y)) / 2),
    @acrule(sinh(~x) * cosh(~y) => (sinh(~x + ~y) + sinh(~x - ~y)) / 2),

    # ── Exponential product/power rules (kept from TRIG_EXP_RULES) ──
    @acrule(exp(~x) * exp(~y) => _iszero(~x + ~y) ? 1 : exp(~x + ~y)),
    @rule(exp(~x)^(~y) => exp(~x * ~y)),
)

const TRIG_REDUCE_SIMPLIFIER = Chain(TRIG_REDUCE_RULES)

"""
    _involves_vars(x, target_vars)

Return `true` if the symbolic expression `x` contains any of the variables in
`target_vars`.  Used by `trig_reduce(; vars=...)` to selectively reduce only
trig functions whose arguments involve the specified variables.
"""
function _involves_vars(x, target_vars)
    buf = BasicSymbolic{SymReal}[]
    search_variables!(buf, unwrap(x))
    for v in buf, tv in target_vars
        isequal(v, unwrap(tv)) && return true
    end
    return false
end

"""
    _build_filtered_trig_reduce(target_vars)

Build a `Chain` of trig-reduce rules that only fire when the trig argument
involves at least one of `target_vars`.
"""
function _build_filtered_trig_reduce(target_vars)
    sp(x) = _involves_vars(x, target_vars)

    rules = (
        # ── Cleanup (always applies) ──
        @rule(sin(~x::_iszero) => 0),
        @rule(cos(~x::_iszero) => 1),
        @rule(sinh(~x::_iszero) => 0),
        @rule(cosh(~x::_iszero) => 1),
        @rule(cos(~x::_has_neg_leading) => cos(-1 * ~x)),
        @rule(sin(~x::_has_neg_leading) => -1 * sin(-1 * ~x)),
        @rule(cosh(~x::_has_neg_leading) => cosh(-1 * ~x)),
        @rule(sinh(~x::_has_neg_leading) => -1 * sinh(-1 * ~x)),

        # ── Power reduction (guarded by vars) ──
        @rule(cos(~x)^(~n::_isinteger_ge2) => sp(~x) ? _trig_power_reduce(cos, ~x, ~n) : nothing),
        @rule(sin(~x)^(~n::_isinteger_ge2) => sp(~x) ? _trig_power_reduce(sin, ~x, ~n) : nothing),
        @rule(cosh(~x)^(~n::_isinteger_ge2) => sp(~x) ? _trig_power_reduce(cosh, ~x, ~n) : nothing),
        @rule(sinh(~x)^(~n::_isinteger_ge2) => sp(~x) ? _trig_power_reduce(sinh, ~x, ~n) : nothing),
        @rule(tan(~x)^2 => sp(~x) ? sec(~x)^2 - 1 : nothing),
        @rule(cot(~x)^2 => sp(~x) ? csc(~x)^2 - 1 : nothing),

        # ── Product-to-sum: circular (guarded) ──
        @acrule(cos(~x) * cos(~y) => (sp(~x) || sp(~y)) ? (cos(~x - ~y) + cos(~x + ~y)) / 2 : nothing),
        @acrule(sin(~x) * sin(~y) => (sp(~x) || sp(~y)) ? (cos(~x - ~y) - cos(~x + ~y)) / 2 : nothing),
        @acrule(sin(~x) * cos(~y) => (sp(~x) || sp(~y)) ? (sin(~x + ~y) + sin(~x - ~y)) / 2 : nothing),

        # ── Product-to-sum: hyperbolic (guarded) ──
        @acrule(cosh(~x) * cosh(~y) => (sp(~x) || sp(~y)) ? (cosh(~x - ~y) + cosh(~x + ~y)) / 2 : nothing),
        @acrule(sinh(~x) * sinh(~y) => (sp(~x) || sp(~y)) ? (cosh(~x + ~y) - cosh(~x - ~y)) / 2 : nothing),
        @acrule(sinh(~x) * cosh(~y) => (sp(~x) || sp(~y)) ? (sinh(~x + ~y) + sinh(~x - ~y)) / 2 : nothing),

        # ── Exponential (always applies) ──
        @acrule(exp(~x) * exp(~y) => _iszero(~x + ~y) ? 1 : exp(~x + ~y)),
        @rule(exp(~x)^(~y) => exp(~x * ~y)),
    )
    return Chain(rules)
end

const BOOLEAN_SIMPLIFIER = Chain(BOOLEAN_RULES)


function get_default_simplifier(; trig_reduce=false, trig_reduce_vars=nothing, kw...)
    trig_chain = if trig_reduce && trig_reduce_vars !== nothing
        Chain((NUMBER_SIMPLIFIER, _build_filtered_trig_reduce(trig_reduce_vars)))
    elseif trig_reduce
        Chain((NUMBER_SIMPLIFIER, TRIG_REDUCE_SIMPLIFIER))
    else
        Chain((NUMBER_SIMPLIFIER, TRIG_EXP_SIMPLIFIER))
    end
    IfElse(has_trig_exp,
           Postwalk(IfElse(x->symtype(x) <: Number,
                           trig_chain,
                           If(x->symtype(x) <: Bool, BOOLEAN_SIMPLIFIER))
                    ; kw...),
           Postwalk(Chain((If(x->symtype(x) <: Number,
                              NUMBER_SIMPLIFIER),
                           If(x->symtype(x) <: Bool,
                              BOOLEAN_SIMPLIFIER)))
                    ; kw...))
end

# reduce overhead of simplify by defining these as constant
const serial_simplifier = If(iscall, Fixpoint(get_default_simplifier()))

threaded_simplifier(cutoff; trig_reduce=false) =
    Fixpoint(get_default_simplifier(trig_reduce=trig_reduce,
                                    threaded=true, thread_cutoff=cutoff))

const serial_expand_simplifier = If(iscall,
                                  Fixpoint(Chain((expand,
                                                  Fixpoint(get_default_simplifier())))))

# Pre-compiled trig_reduce simplifiers (opt-in path)
const serial_trig_reduce_simplifier =
    If(iscall, Fixpoint(Chain((expand,
                               Fixpoint(get_default_simplifier(trig_reduce=true))))))

const serial_expand_trig_reduce_simplifier =
    If(iscall, Fixpoint(Chain((expand,
                               Fixpoint(get_default_simplifier(trig_reduce=true))))))
