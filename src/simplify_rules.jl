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

_has_trig_sum(ex) = isadd(ex) && has_trig_exp(ex)

function _square_of(f, factor)
    ispow(factor) || return nothing
    base, power = arguments(factor)
    iscall(base) && operation(base) === f && isequal(unwrap_const(power), 2) || return nothing
    return only(arguments(base))
end

# Whether a pairwise rule below (`~r*~x::has_trig_exp + ~r*~y` or `sin(~x)^2 + cos(~x)^2`)
# applies. Those rewrites are cheaper than re-simplifying the whole sum after
# `_factor_common_trig_term` pulls out a common factor, so they go first.
function _has_pairwise_trig_rewrite(args)
    scaled = Dict{eltype(args), Bool}()
    sin_squares = Set{eltype(args)}()
    cos_squares = eltype(args)[]
    for term in args
        if ismul(term)
            factors = arguments(term)
            length(factors) == 2 || continue
            for (factor, other) in ((factors[1], factors[2]), (factors[2], factors[1]))
                trig = has_trig_exp(other)
                seen = get(scaled, factor, nothing)
                seen !== nothing && (seen || trig) && return true
                scaled[factor] = trig
            end
        else
            x = _square_of(sin, term)
            x === nothing || push!(sin_squares, x)
            x = _square_of(cos, term)
            x === nothing || push!(cos_squares, x)
        end
    end
    return any(in(sin_squares), cos_squares)
end

function _factor_common_trig_term(ex::BasicSymbolic{T}) where {T}
    args = collect(arguments(ex))
    _has_pairwise_trig_rewrite(args) && return nothing
    factors = Vector{Accumulator{BasicSymbolic{T}, Int}}(undef, length(args))
    smallest = firstindex(factors)
    for (i, term) in enumerate(args)
        term_factors = counter(BasicSymbolic{T})
        for factor in (ismul(term) ? parent(arguments(term)) : ArgsT{T}((term,)))
            push!(term_factors, factor)
        end
        factors[i] = term_factors
        if length(term_factors) < length(factors[smallest])
            smallest = i
        end
    end

    common_counts = copy(factors[smallest])
    for term_factors in factors
        intersect!(common_counts, term_factors)
        isempty(common_counts) && return nothing
    end

    common = BasicSymbolic{T}[]
    for (candidate, multiplicity) in common_counts
        for _ in 1:multiplicity
            push!(common, candidate)
        end
    end
    remainder_factors = BasicSymbolic{T}[]
    map!(args, factors) do term_factors
        empty!(remainder_factors)
        for (factor, multiplicity) in setdiff(term_factors, common_counts)
            for _ in 1:multiplicity
                push!(remainder_factors, factor)
            end
        end
        isempty(remainder_factors) ? one_of_vartype(T) : mul_worker(T, remainder_factors)
    end
    any(has_trig_exp, args) || return nothing
    push!(common, add_worker(T, args))
    return mul_worker(T, common)
end

const TRIG_EXP_RULES = (
    @acrule(~r*~x::has_trig_exp + ~r*~y => ~r*(~x + ~y)),
    @acrule(~r*~x::has_trig_exp + -1*~r*~y => ~r*(~x - ~y)),
    @acrule(sin(~x)^2 + cos(~x)^2 => one(~x)),
    # Mul(-1, Add(...)) distributes -1 into the Add, so a direct scaled rule is needed.
    @acrule(~r*sin(~x)^2 + ~r*cos(~x)^2 => ~r),
    @rule(~x::_has_trig_sum => _factor_common_trig_term(~x)),
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
    _is_odd_half_pi(x)

Return `true` if `x` is an odd multiple of π/2 (±π/2, ±3π/2, ±5π/2, …)
that is NOT an integer multiple of π.  Used by the quarter-period shift rules
(co-function identities like sin(x+π/2) → cos(x)).
"""
function _is_odd_half_pi(x)
    v = _to_number(x)
    v === nothing && return false
    n = v / (π/2)
    return (abs(round(n) - n) < 1e-9 && isodd(Int(round(n))))::Bool
end

"""
    _half_pi_shift_sign(y)

For an odd multiple of π/2, return +1 if y ≡ π/2 (mod 2π) and -1 if
y ≡ 3π/2 (mod 2π).  This determines the sign in co-function identities:
sin(x + y) = ±cos(x), cos(x + y) = ∓sin(x).
"""
function _half_pi_shift_sign(y)
    v = _to_number(y)
    v === nothing && return 0
    n = Int(round(v / (π/2)))
    return mod(n, 4) == 1 ? 1 : -1
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

"""
    _any_trig(args...)

Return `true` if any argument contains a trig or exp function.
Used by the conditional fallback rules to only convert `tan`/`cot`/`sec`/`csc`
to `sin`/`cos` when they appear in a product with another trig expression,
not when they are bare or multiplied only by scalars.
"""
_any_trig(args...) = any(a -> a isa BasicSymbolic && has_trig_exp(a), args)

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
    @rule(cot(~x::_has_neg_leading) => -1 * cot(-1 * ~x)),   # cot is odd
    @rule(sec(~x::_has_neg_leading) => sec(-1 * ~x)),         # sec is even
    @rule(csc(~x::_has_neg_leading) => -1 * csc(-1 * ~x)),   # csc is odd
    @rule(cosh(~x::_has_neg_leading) => cosh(-1 * ~x)),      # cosh is even
    @rule(sinh(~x::_has_neg_leading) => -1 * sinh(-1 * ~x)), # sinh is odd
    @rule(tanh(~x::_has_neg_leading) => -1 * tanh(-1 * ~x)), # tanh is odd
    @rule(coth(~x::_has_neg_leading) => -1 * coth(-1 * ~x)), # coth is odd
    @rule(sech(~x::_has_neg_leading) => sech(-1 * ~x)),      # sech is even
    @rule(csch(~x::_has_neg_leading) => -1 * csch(-1 * ~x)), # csch is odd

    # ── Period reduction: remove integer multiples of π from trig arguments ──
    # NOTE: only handles integer multiples of π (π, 2π, 3π, …).
    # Rational multiples (π/2, π/3, …) are not yet supported.
    # sin/cos: period 2π, sign flip at odd multiples of π
    @rule(sin(~~a + ~y::_is_nonzero_even_multiple_of_pi + ~~b) => sin(+(~~a..., ~~b...))),
    @rule(sin(~~a + ~y::_is_odd_multiple_of_pi + ~~b) => -sin(+(~~a..., ~~b...))),
    @rule(cos(~~a + ~y::_is_nonzero_even_multiple_of_pi + ~~b) => cos(+(~~a..., ~~b...))),
    @rule(cos(~~a + ~y::_is_odd_multiple_of_pi + ~~b) => -cos(+(~~a..., ~~b...))),
    # tan/cot: period π
    @rule(tan(~~a + ~y::_is_odd_multiple_of_pi + ~~b) => tan(+(~~a..., ~~b...))),
    @rule(tan(~~a + ~y::_is_nonzero_even_multiple_of_pi + ~~b) => tan(+(~~a..., ~~b...))),
    @rule(cot(~~a + ~y::_is_odd_multiple_of_pi + ~~b) => cot(+(~~a..., ~~b...))),
    @rule(cot(~~a + ~y::_is_nonzero_even_multiple_of_pi + ~~b) => cot(+(~~a..., ~~b...))),
    # sec/csc: period 2π, sign flip at odd multiples of π
    @rule(sec(~~a + ~y::_is_odd_multiple_of_pi + ~~b) => -sec(+(~~a..., ~~b...))),
    @rule(sec(~~a + ~y::_is_nonzero_even_multiple_of_pi + ~~b) => sec(+(~~a..., ~~b...))),
    @rule(csc(~~a + ~y::_is_odd_multiple_of_pi + ~~b) => -csc(+(~~a..., ~~b...))),
    @rule(csc(~~a + ~y::_is_nonzero_even_multiple_of_pi + ~~b) => csc(+(~~a..., ~~b...))),

    # ── Quarter-period shifts: co-function identities for odd multiples of π/2 ──
    # sin(x+π/2) = cos(x), sin(x+3π/2) = -cos(x), etc.
    # NOTE: rational multiples of π other than n*π/2 (e.g. π/3, π/4, π/6)
    # are not yet handled; Mathematica also mostly leaves those as-is.
    @rule(sin(~~a + ~y::_is_odd_half_pi + ~~b) => _half_pi_shift_sign(~y) * cos(+(~~a..., ~~b...))),
    @rule(cos(~~a + ~y::_is_odd_half_pi + ~~b) => -_half_pi_shift_sign(~y) * sin(+(~~a..., ~~b...))),
    @rule(tan(~~a + ~y::_is_odd_half_pi + ~~b) => -cot(+(~~a..., ~~b...))),
    @rule(cot(~~a + ~y::_is_odd_half_pi + ~~b) => -tan(+(~~a..., ~~b...))),
    @rule(sec(~~a + ~y::_is_odd_half_pi + ~~b) => -_half_pi_shift_sign(~y) * csc(+(~~a..., ~~b...))),
    @rule(csc(~~a + ~y::_is_odd_half_pi + ~~b) => _half_pi_shift_sign(~y) * sec(+(~~a..., ~~b...))),

    # ── Power reduction: f(x)^n for n ≥ 2 ──
    # Circular
    @rule(cos(~x)^(~n::_isinteger_ge2) => _trig_power_reduce(cos, ~x, ~n)),
    @rule(sin(~x)^(~n::_isinteger_ge2) => _trig_power_reduce(sin, ~x, ~n)),
    @rule(tan(~x)^(~n::_isinteger_ge2) => _trig_power_reduce(tan, ~x, ~n)),
    @rule(cot(~x)^(~n::_isinteger_ge2) => _trig_power_reduce(cot, ~x, ~n)),
    @rule(sec(~x)^(~n::_isinteger_ge2) => 1 / _trig_power_reduce(cos, ~x, ~n)),
    @rule(csc(~x)^(~n::_isinteger_ge2) => 1 / _trig_power_reduce(sin, ~x, ~n)),
    # Hyperbolic
    @rule(cosh(~x)^(~n::_isinteger_ge2) => _trig_power_reduce(cosh, ~x, ~n)),
    @rule(sinh(~x)^(~n::_isinteger_ge2) => _trig_power_reduce(sinh, ~x, ~n)),
    @rule(tanh(~x)^(~n::_isinteger_ge2) => _trig_power_reduce(tanh, ~x, ~n)),
    @rule(coth(~x)^(~n::_isinteger_ge2) => _trig_power_reduce(coth, ~x, ~n)),
    @rule(sech(~x)^(~n::_isinteger_ge2) => 1 / _trig_power_reduce(cosh, ~x, ~n)),
    @rule(csch(~x)^(~n::_isinteger_ge2) => 1 / _trig_power_reduce(sinh, ~x, ~n)),

    # ── Same-argument cancellation rules ──
    @acrule(tan(~x) * cos(~x) => sin(~x)),
    @acrule(cot(~x) * sin(~x) => cos(~x)),
    @acrule(sec(~x) * cos(~x) => 1),
    @acrule(csc(~x) * sin(~x) => 1),
    @acrule(tan(~x) * cot(~x) => 1),
    @acrule(sec(~x) * sin(~x) => tan(~x)),
    @acrule(csc(~x) * cos(~x) => cot(~x)),
    @acrule(tan(~x) * csc(~x) => sec(~x)),
    @acrule(cot(~x) * sec(~x) => csc(~x)),

    # ── Dual-conversion rules: products of two non-sin/cos functions ──
    # Convert both to sin/cos simultaneously so product-to-sum +
    # simplify_fractions can handle the result in subsequent iterations.
    # General ~x/~y rules also cover same-arg (cancellation rules above
    # take precedence when they apply).
    @acrule(tan(~x) * sec(~y) => sin(~x) / (cos(~x) * cos(~y))),
    @acrule(tan(~x) * csc(~y) => sin(~x) / (cos(~x) * sin(~y))),
    @acrule(cot(~x) * sec(~y) => cos(~x) / (sin(~x) * cos(~y))),
    @acrule(cot(~x) * csc(~y) => cos(~x) / (sin(~x) * sin(~y))),
    @acrule(sec(~x) * csc(~y) => 1 / (cos(~x) * sin(~y))),
    @acrule(sec(~x) * sec(~y) => 1 / (cos(~x) * cos(~y))),
    @acrule(csc(~x) * csc(~y) => 1 / (sin(~x) * sin(~y))),

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

    # ── Conditional fallback: convert tan/cot/sec/csc to sin/cos ONLY ──
    # when they appear in a product with another trig expression.
    # Bare functions (tan(x), 3*tan(x), r*sec(x)) are left as-is.
    @acrule(tan(~x) * ~~y => _any_trig(~~y...) ? sin(~x) / cos(~x) * *(~~y...) : nothing),
    @acrule(cot(~x) * ~~y => _any_trig(~~y...) ? cos(~x) / sin(~x) * *(~~y...) : nothing),
    @acrule(sec(~x) * ~~y => _any_trig(~~y...) ? 1 / cos(~x) * *(~~y...) : nothing),
    @acrule(csc(~x) * ~~y => _any_trig(~~y...) ? 1 / sin(~x) * *(~~y...) : nothing),
    @acrule(tanh(~x) * ~~y => _any_trig(~~y...) ? sinh(~x) / cosh(~x) * *(~~y...) : nothing),
    @acrule(coth(~x) * ~~y => _any_trig(~~y...) ? cosh(~x) / sinh(~x) * *(~~y...) : nothing),
    @acrule(sech(~x) * ~~y => _any_trig(~~y...) ? 1 / cosh(~x) * *(~~y...) : nothing),
    @acrule(csch(~x) * ~~y => _any_trig(~~y...) ? 1 / sinh(~x) * *(~~y...) : nothing),
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
        @rule(cot(~x::_has_neg_leading) => -1 * cot(-1 * ~x)),
        @rule(sec(~x::_has_neg_leading) => sec(-1 * ~x)),
        @rule(csc(~x::_has_neg_leading) => -1 * csc(-1 * ~x)),
        @rule(cosh(~x::_has_neg_leading) => cosh(-1 * ~x)),
        @rule(sinh(~x::_has_neg_leading) => -1 * sinh(-1 * ~x)),
        @rule(tanh(~x::_has_neg_leading) => -1 * tanh(-1 * ~x)),
        @rule(coth(~x::_has_neg_leading) => -1 * coth(-1 * ~x)),
        @rule(sech(~x::_has_neg_leading) => sech(-1 * ~x)),
        @rule(csch(~x::_has_neg_leading) => -1 * csch(-1 * ~x)),

        # ── Period reduction ──
        @rule(sin(~~a + ~y::_is_nonzero_even_multiple_of_pi + ~~b) => sin(+(~~a..., ~~b...))),
        @rule(sin(~~a + ~y::_is_odd_multiple_of_pi + ~~b) => -sin(+(~~a..., ~~b...))),
        @rule(cos(~~a + ~y::_is_nonzero_even_multiple_of_pi + ~~b) => cos(+(~~a..., ~~b...))),
        @rule(cos(~~a + ~y::_is_odd_multiple_of_pi + ~~b) => -cos(+(~~a..., ~~b...))),
        @rule(tan(~~a + ~y::_is_odd_multiple_of_pi + ~~b) => tan(+(~~a..., ~~b...))),
        @rule(tan(~~a + ~y::_is_nonzero_even_multiple_of_pi + ~~b) => tan(+(~~a..., ~~b...))),
        @rule(cot(~~a + ~y::_is_odd_multiple_of_pi + ~~b) => cot(+(~~a..., ~~b...))),
        @rule(cot(~~a + ~y::_is_nonzero_even_multiple_of_pi + ~~b) => cot(+(~~a..., ~~b...))),
        @rule(sec(~~a + ~y::_is_odd_multiple_of_pi + ~~b) => -sec(+(~~a..., ~~b...))),
        @rule(sec(~~a + ~y::_is_nonzero_even_multiple_of_pi + ~~b) => sec(+(~~a..., ~~b...))),
        @rule(csc(~~a + ~y::_is_odd_multiple_of_pi + ~~b) => -csc(+(~~a..., ~~b...))),
        @rule(csc(~~a + ~y::_is_nonzero_even_multiple_of_pi + ~~b) => csc(+(~~a..., ~~b...))),

        # ── Quarter-period shifts ──
        @rule(sin(~~a + ~y::_is_odd_half_pi + ~~b) => _half_pi_shift_sign(~y) * cos(+(~~a..., ~~b...))),
        @rule(cos(~~a + ~y::_is_odd_half_pi + ~~b) => -_half_pi_shift_sign(~y) * sin(+(~~a..., ~~b...))),
        @rule(tan(~~a + ~y::_is_odd_half_pi + ~~b) => -cot(+(~~a..., ~~b...))),
        @rule(cot(~~a + ~y::_is_odd_half_pi + ~~b) => -tan(+(~~a..., ~~b...))),
        @rule(sec(~~a + ~y::_is_odd_half_pi + ~~b) => -_half_pi_shift_sign(~y) * csc(+(~~a..., ~~b...))),
        @rule(csc(~~a + ~y::_is_odd_half_pi + ~~b) => _half_pi_shift_sign(~y) * sec(+(~~a..., ~~b...))),

        # ── Power reduction (guarded by vars) ──
        @rule(cos(~x)^(~n::_isinteger_ge2) => sp(~x) ? _trig_power_reduce(cos, ~x, ~n) : nothing),
        @rule(sin(~x)^(~n::_isinteger_ge2) => sp(~x) ? _trig_power_reduce(sin, ~x, ~n) : nothing),
        @rule(tan(~x)^(~n::_isinteger_ge2) => sp(~x) ? _trig_power_reduce(tan, ~x, ~n) : nothing),
        @rule(cot(~x)^(~n::_isinteger_ge2) => sp(~x) ? _trig_power_reduce(cot, ~x, ~n) : nothing),
        @rule(sec(~x)^(~n::_isinteger_ge2) => sp(~x) ? 1 / _trig_power_reduce(cos, ~x, ~n) : nothing),
        @rule(csc(~x)^(~n::_isinteger_ge2) => sp(~x) ? 1 / _trig_power_reduce(sin, ~x, ~n) : nothing),
        @rule(cosh(~x)^(~n::_isinteger_ge2) => sp(~x) ? _trig_power_reduce(cosh, ~x, ~n) : nothing),
        @rule(sinh(~x)^(~n::_isinteger_ge2) => sp(~x) ? _trig_power_reduce(sinh, ~x, ~n) : nothing),
        @rule(tanh(~x)^(~n::_isinteger_ge2) => sp(~x) ? _trig_power_reduce(tanh, ~x, ~n) : nothing),
        @rule(coth(~x)^(~n::_isinteger_ge2) => sp(~x) ? _trig_power_reduce(coth, ~x, ~n) : nothing),
        @rule(sech(~x)^(~n::_isinteger_ge2) => sp(~x) ? 1 / _trig_power_reduce(cosh, ~x, ~n) : nothing),
        @rule(csch(~x)^(~n::_isinteger_ge2) => sp(~x) ? 1 / _trig_power_reduce(sinh, ~x, ~n) : nothing),

        # ── Same-argument cancellation rules (guarded) ──
        @acrule(tan(~x) * cos(~x) => sp(~x) ? sin(~x) : nothing),
        @acrule(cot(~x) * sin(~x) => sp(~x) ? cos(~x) : nothing),
        @acrule(sec(~x) * cos(~x) => sp(~x) ? 1 : nothing),
        @acrule(csc(~x) * sin(~x) => sp(~x) ? 1 : nothing),
        @acrule(tan(~x) * cot(~x) => sp(~x) ? 1 : nothing),
        @acrule(sec(~x) * sin(~x) => sp(~x) ? tan(~x) : nothing),
        @acrule(csc(~x) * cos(~x) => sp(~x) ? cot(~x) : nothing),
        @acrule(tan(~x) * csc(~x) => sp(~x) ? sec(~x) : nothing),
        @acrule(cot(~x) * sec(~x) => sp(~x) ? csc(~x) : nothing),

        # ── Dual-conversion rules (guarded) ──
        @acrule(tan(~x) * sec(~y) => (sp(~x) || sp(~y)) ? sin(~x) / (cos(~x) * cos(~y)) : nothing),
        @acrule(tan(~x) * csc(~y) => (sp(~x) || sp(~y)) ? sin(~x) / (cos(~x) * sin(~y)) : nothing),
        @acrule(cot(~x) * sec(~y) => (sp(~x) || sp(~y)) ? cos(~x) / (sin(~x) * cos(~y)) : nothing),
        @acrule(cot(~x) * csc(~y) => (sp(~x) || sp(~y)) ? cos(~x) / (sin(~x) * sin(~y)) : nothing),
        @acrule(sec(~x) * csc(~y) => (sp(~x) || sp(~y)) ? 1 / (cos(~x) * sin(~y)) : nothing),
        @acrule(sec(~x) * sec(~y) => (sp(~x) || sp(~y)) ? 1 / (cos(~x) * cos(~y)) : nothing),
        @acrule(csc(~x) * csc(~y) => (sp(~x) || sp(~y)) ? 1 / (sin(~x) * sin(~y)) : nothing),

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

        # ── Conditional fallback (guarded) ──
        @acrule(tan(~x) * ~~y => (sp(~x) && _any_trig(~~y...)) ? sin(~x) / cos(~x) * *(~~y...) : nothing),
        @acrule(cot(~x) * ~~y => (sp(~x) && _any_trig(~~y...)) ? cos(~x) / sin(~x) * *(~~y...) : nothing),
        @acrule(sec(~x) * ~~y => (sp(~x) && _any_trig(~~y...)) ? 1 / cos(~x) * *(~~y...) : nothing),
        @acrule(csc(~x) * ~~y => (sp(~x) && _any_trig(~~y...)) ? 1 / sin(~x) * *(~~y...) : nothing),
        @acrule(tanh(~x) * ~~y => (sp(~x) && _any_trig(~~y...)) ? sinh(~x) / cosh(~x) * *(~~y...) : nothing),
        @acrule(coth(~x) * ~~y => (sp(~x) && _any_trig(~~y...)) ? cosh(~x) / sinh(~x) * *(~~y...) : nothing),
        @acrule(sech(~x) * ~~y => (sp(~x) && _any_trig(~~y...)) ? 1 / cosh(~x) * *(~~y...) : nothing),
        @acrule(csch(~x) * ~~y => (sp(~x) && _any_trig(~~y...)) ? 1 / sinh(~x) * *(~~y...) : nothing),
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
