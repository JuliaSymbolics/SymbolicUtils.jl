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
    # sqrt(x^2) = |x| on reals; for complex, sqrt(z^2) = ±z ≠ |z|
    @rule(sqrt((~x::_isreal)^2) => abs(~x)),
    # |x|^2 = x^2 for reals; for complex, |z|^2 = z*conj(z) ≠ z^2
    @rule((abs(~x::_isreal))^2 => (~x)^2),
)

# Unary minus canonicalizes to *(-1, x), so abs(-x) is abs(*(-1, x)).
_is_neg_literal(x) = _isnegative(unwrap_const(x))

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
    @rule(abs(abs(~x)) => abs(~x)),
    @rule(abs(*(~c::_is_neg_literal, ~~xs)) => abs(*(-unwrap_const(~c), (~~xs)...))),
    # literal sqrt(...) never reaches POW_RULES (gated on ^); Real only
    @rule(sqrt((~x::_isreal)^2) => abs(~x)),
    @rule(abs(~x::is_literal_number) => abs(~x)),
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
    # a - a*trig²(x). Same-slot alone misses flattened 2+(-2)*cos²; unconstrained
    # segment ~~b is too slow on large sums. Literal two-slot + same-slot only.
    # ~a::(!has_trig_exp) cuts AC attempts that bind ~a to a trig term.
    @acrule(~a::is_literal_number + ~b::is_literal_number*cos(~x)^2 => _literal_negates(~a, ~b) ? ~a*sin(~x)^2 : nothing),
    @acrule(~a::(!has_trig_exp) + -1*~a*cos(~x)^2 => ~a*sin(~x)^2),
    @acrule(~a::is_literal_number + ~b::is_literal_number*sin(~x)^2 => _literal_negates(~a, ~b) ? ~a*cos(~x)^2 : nothing),
    @acrule(~a::(!has_trig_exp) + -1*~a*sin(~x)^2 => ~a*cos(~x)^2),

    @acrule(cos(~x)^2 + -1*sin(~x)^2 => cos(2 * ~x)),
    @acrule(sin(~x)^2 + -1*cos(~x)^2 => -cos(2 * ~x)),
    @acrule(cos(~x) * sin(~x) => sin(2 * ~x)/2),

    @acrule(tan(~x)^2 + -1*sec(~x)^2 => -one(~x)),
    @acrule(-1*tan(~x)^2 + sec(~x)^2 => one(~x)),
    @acrule(tan(~x)^2 +  1 => sec(~x)^2),
    @acrule(sec(~x)^2 + -1 => tan(~x)^2),

    @acrule(cot(~x)^2 + -1*csc(~x)^2 => -one(~x)),
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

For `tan`, `cot`, `tanh`, `coth` the half-angle identities produce ratios of
`cos`/`cosh` terms, which the subsequent linearization and `simplify_fractions`
steps will simplify:

    tan(x)^2  = (1 - cos(2x)) / (1 + cos(2x))
    cot(x)^2  = (1 + cos(2x)) / (1 - cos(2x))
    tanh(x)^2 = (cosh(2x) - 1) / (cosh(2x) + 1)
    coth(x)^2 = (cosh(2x) + 1) / (cosh(2x) - 1)
"""
function _trig_power_reduce(@nospecialize(f), x::BasicSymbolic{T}, n) where {T}
    k = div(n, 2)   # number of squared pairs
    r = rem(n, 2)   # leftover power (0 or 1)
    if f === cos
        sq = (1 + cos(2 * x)) / 2
    elseif f === sin
        sq = (1 - cos(2 * x)) / 2
    elseif f === tan
        sq = (1 - cos(2 * x)) / (1 + cos(2 * x))
    elseif f === cot
        sq = (1 + cos(2 * x)) / (1 - cos(2 * x))
    elseif f === cosh
        sq = (1 + cosh(2 * x)) / 2
    elseif f === sinh
        sq = (cosh(2 * x) - 1) / 2
    elseif f === tanh
        sq = (cosh(2 * x) - 1) / (cosh(2 * x) + 1)
    elseif f === coth
        sq = (cosh(2 * x) + 1) / (cosh(2 * x) - 1)
    else
        return nothing
    end
    return (f(x)::BasicSymbolic{T})^r * sq^k
end

_isinteger_ge2(@nospecialize(n)) = n isa Integer && (n >= 2)::Bool

"""
    _to_number(x)

Extract the numeric value from a symbolic constant wrapper. Handles both
`Const(val)` and the `identity(Const(val))` wrapping that SymbolicUtils uses
for irrational constants like `π`.  Returns `nothing` for non-constant terms.
"""
function _to_number(x)
    v = unwrap_const(x)
    v isa Number && return v
    if x isa BasicSymbolic && iscall(x) && operation(x) === identity
        arg = arguments(x)[1]
        isconst(arg) && return unwrap_const(arg)
    end
    return nothing
end

"""
    _is_odd_multiple_of_pi(x)

Return `true` if `x` is an odd multiple of π (±π, ±3π, …).
Used by the period-reduction cleanup rules.
"""
function _is_odd_multiple_of_pi(x)
    v = _to_number(x)
    v === nothing && return false
    n = v / π
    return (abs(round(n) - n) < 1e-9 && isodd(Int(round(n))))::Bool
end

"""
    _is_nonzero_even_multiple_of_pi(x)

Return `true` if `x` is a nonzero even multiple of π (±2π, ±4π, …).
Used by the period-reduction cleanup rules.
"""
function _is_nonzero_even_multiple_of_pi(x)
    v = _to_number(x)
    v === nothing && return false
    n = v / π
    nn = round(n)
    return (abs(nn - n) < 1e-9 && iseven(Int(nn)) && !iszero(Int(nn)))::Bool
end

"""
    _is_neg_term(v)

Return `true` if the numeric coefficient `v` counts as "negative" for the
majority vote in `_has_neg_leading`. Real numbers use the usual sign check.
Complex numbers have no total order, so we fall back to the sign of the real
part, and the sign of the imaginary part if the real part is zero (matching
how e.g. `-im` is considered negative). Zero (in either sense) doesn't count
as negative.
"""
function _is_neg_term(v)
    v isa Real && return (v < 0)::Bool
    if v isa Complex
        rv = real(v)
        !_iszero(rv) && return (rv < 0)::Bool
        return (imag(v) < 0)::Bool
    end
    return false
end

"""
    _has_neg_leading(x)

Return `true` if `x` "looks negative": a negative number, a Mul with a
negative numeric coefficient, or an Add with more negative terms than
positive ones.

For `ADD`, `dict` (an `ACDict`, i.e. a plain `Dict`) has no deterministic
iteration order, so instead of picking out a single "leading term" we take a
majority vote over the sign of every term (including the constant `coeff`,
if nonzero): `x` is treated as negative if strictly more terms are negative
than positive. Complex terms are handled via `_is_neg_term` (sign of the real
part, falling back to the imaginary part). Ties (equal counts, or no terms at
all) are treated as non-negative.

Used to canonicalise `cos(-expr) → cos(expr)` and `sin(-expr) → -sin(expr)`.
"""
function _has_neg_leading(x)
    x = unwrap_const(x)
    x isa Real && return (x < 0)::Bool
    x isa BasicSymbolic || return false
    @match x begin
        BSImpl.Const(; val) => return val isa Real && (val < 0)::Bool
        BSImpl.AddMul(; coeff, dict, variant) => begin
            if variant === AddMulVariant.MUL
                return coeff isa Real && (coeff < 0)::Bool
            else
                neg = 0
                pos = 0
                if !_iszero(coeff)
                    _is_neg_term(coeff) ? (neg += 1) : (pos += 1)
                end
                for v in values(dict)
                    _iszero(v) && continue
                    _is_neg_term(v) ? (neg += 1) : (pos += 1)
                end
                return neg > pos
            end
        end
        _ => return false
    end
end

const TRIG_REDUCE_RULES = (
    # ── Cleanup: fold literal values, normalize negative arguments ──
    @rule(sin(~x::_iszero) => 0),
    @rule(cos(~x::_iszero) => 1),
    @rule(tan(~x::_iszero) => 0),
    @rule(sinh(~x::_iszero) => 0),
    @rule(cosh(~x::_iszero) => 1),
    @rule(tanh(~x::_iszero) => 0),
    @rule(cos(~x::_has_neg_leading) => cos(-1 * ~x)),        # cos is even
    @rule(sin(~x::_has_neg_leading) => -1 * sin(-1 * ~x)),   # sin is odd
    @rule(tan(~x::_has_neg_leading) => -1 * tan(-1 * ~x)),   # tan is odd
    @rule(cosh(~x::_has_neg_leading) => cosh(-1 * ~x)),      # cosh is even
    @rule(sinh(~x::_has_neg_leading) => -1 * sinh(-1 * ~x)), # sinh is odd
    @rule(tanh(~x::_has_neg_leading) => -1 * tanh(-1 * ~x)), # tanh is odd

    # ── Period reduction: remove multiples of π from trig arguments ──
    @rule(sin(~~a + ~y::_is_nonzero_even_multiple_of_pi + ~~b) => sin(+(~~a..., ~~b...))),
    @rule(sin(~~a + ~y::_is_odd_multiple_of_pi + ~~b) => -sin(+(~~a..., ~~b...))),
    @rule(cos(~~a + ~y::_is_nonzero_even_multiple_of_pi + ~~b) => cos(+(~~a..., ~~b...))),
    @rule(cos(~~a + ~y::_is_odd_multiple_of_pi + ~~b) => -cos(+(~~a..., ~~b...))),

    # ── Power reduction: f(x)^n for n ≥ 2 ──
    # Circular
    @rule(cos(~x)^(~n::_isinteger_ge2) => _trig_power_reduce(cos, ~x, ~n)),
    @rule(sin(~x)^(~n::_isinteger_ge2) => _trig_power_reduce(sin, ~x, ~n)),
    @rule(tan(~x)^(~n::_isinteger_ge2) => _trig_power_reduce(tan, ~x, ~n)),
    @rule(cot(~x)^(~n::_isinteger_ge2) => _trig_power_reduce(cot, ~x, ~n)),
    # Hyperbolic
    @rule(cosh(~x)^(~n::_isinteger_ge2) => _trig_power_reduce(cosh, ~x, ~n)),
    @rule(sinh(~x)^(~n::_isinteger_ge2) => _trig_power_reduce(sinh, ~x, ~n)),
    @rule(tanh(~x)^(~n::_isinteger_ge2) => _trig_power_reduce(tanh, ~x, ~n)),
    @rule(coth(~x)^(~n::_isinteger_ge2) => _trig_power_reduce(coth, ~x, ~n)),

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

    # ── Fallback: convert remaining tan/cot/sec/csc to sin/cos ──
    # These fire on bare tan(x) etc., converting them to sin/cos ratios.
    # For powers like tan(x)^n, the Postwalk visits tan(x) first and
    # converts it, leaving (sin(x)/cos(x))^n which subsequent iterations
    # (expand + power reduction + simplify_fractions) will handle.
    @rule(tan(~x) => sin(~x) / cos(~x)),
    @rule(cot(~x) => cos(~x) / sin(~x)),
    @rule(sec(~x) => 1 / cos(~x)),
    @rule(csc(~x) => 1 / sin(~x)),
    @rule(tanh(~x) => sinh(~x) / cosh(~x)),
    @rule(coth(~x) => cosh(~x) / sinh(~x)),
    @rule(sech(~x) => 1 / cosh(~x)),
    @rule(csch(~x) => 1 / sinh(~x)),
)

const TRIG_REDUCE_SIMPLIFIER = Chain(TRIG_REDUCE_RULES)

"""
    _involves_vars(x, target_vars::AbstractSet)

Return `true` if the symbolic expression `x` contains any of the variables in
`target_vars`.  Uses `query` for efficient short-circuiting tree traversal.
"""
_involves_vars(x, target_vars::AbstractSet) = query(in(target_vars), unwrap(x))

"""
    _build_filtered_trig_reduce(target_vars)

Build a `Chain` of trig-reduce rules that only fire when the trig argument
involves at least one of `target_vars`.
"""
function _build_filtered_trig_reduce(target_vars)
    target_set = Set(unwrap.(target_vars))
    sp(x) = _involves_vars(x, target_set)

    rules = (
        # ── Cleanup (always applies) ──
        @rule(sin(~x::_iszero) => 0),
        @rule(cos(~x::_iszero) => 1),
        @rule(tan(~x::_iszero) => 0),
        @rule(sinh(~x::_iszero) => 0),
        @rule(cosh(~x::_iszero) => 1),
        @rule(tanh(~x::_iszero) => 0),
        @rule(cos(~x::_has_neg_leading) => cos(-1 * ~x)),
        @rule(sin(~x::_has_neg_leading) => -1 * sin(-1 * ~x)),
        @rule(tan(~x::_has_neg_leading) => -1 * tan(-1 * ~x)),
        @rule(cosh(~x::_has_neg_leading) => cosh(-1 * ~x)),
        @rule(sinh(~x::_has_neg_leading) => -1 * sinh(-1 * ~x)),
        @rule(tanh(~x::_has_neg_leading) => -1 * tanh(-1 * ~x)),

        # ── Period reduction ──
        @rule(sin(~~a + ~y::_is_nonzero_even_multiple_of_pi + ~~b) => sin(+(~~a..., ~~b...))),
        @rule(sin(~~a + ~y::_is_odd_multiple_of_pi + ~~b) => -sin(+(~~a..., ~~b...))),
        @rule(cos(~~a + ~y::_is_nonzero_even_multiple_of_pi + ~~b) => cos(+(~~a..., ~~b...))),
        @rule(cos(~~a + ~y::_is_odd_multiple_of_pi + ~~b) => -cos(+(~~a..., ~~b...))),

        # ── Power reduction (guarded by vars) ──
        @rule(cos(~x)^(~n::_isinteger_ge2) => sp(~x) ? _trig_power_reduce(cos, ~x, ~n) : nothing),
        @rule(sin(~x)^(~n::_isinteger_ge2) => sp(~x) ? _trig_power_reduce(sin, ~x, ~n) : nothing),
        @rule(tan(~x)^(~n::_isinteger_ge2) => sp(~x) ? _trig_power_reduce(tan, ~x, ~n) : nothing),
        @rule(cot(~x)^(~n::_isinteger_ge2) => sp(~x) ? _trig_power_reduce(cot, ~x, ~n) : nothing),
        @rule(cosh(~x)^(~n::_isinteger_ge2) => sp(~x) ? _trig_power_reduce(cosh, ~x, ~n) : nothing),
        @rule(sinh(~x)^(~n::_isinteger_ge2) => sp(~x) ? _trig_power_reduce(sinh, ~x, ~n) : nothing),
        @rule(tanh(~x)^(~n::_isinteger_ge2) => sp(~x) ? _trig_power_reduce(tanh, ~x, ~n) : nothing),
        @rule(coth(~x)^(~n::_isinteger_ge2) => sp(~x) ? _trig_power_reduce(coth, ~x, ~n) : nothing),

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

        # ── Fallback: convert remaining tan/cot/sec/csc to sin/cos (guarded) ──
        @rule(tan(~x) => sp(~x) ? sin(~x) / cos(~x) : nothing),
        @rule(cot(~x) => sp(~x) ? cos(~x) / sin(~x) : nothing),
        @rule(sec(~x) => sp(~x) ? 1 / cos(~x) : nothing),
        @rule(csc(~x) => sp(~x) ? 1 / sin(~x) : nothing),
        @rule(tanh(~x) => sp(~x) ? sinh(~x) / cosh(~x) : nothing),
        @rule(coth(~x) => sp(~x) ? cosh(~x) / sinh(~x) : nothing),
        @rule(sech(~x) => sp(~x) ? 1 / cosh(~x) : nothing),
        @rule(csch(~x) => sp(~x) ? 1 / sinh(~x) : nothing),
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

# Pre-compiled trig_reduce simplifier (opt-in path).
# Always includes an expand pass since trig reduction needs expanded inputs.
const serial_trig_reduce_simplifier =
    If(iscall, Fixpoint(Chain((expand,
                               Fixpoint(get_default_simplifier(trig_reduce=true))))))
