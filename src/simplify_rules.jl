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
    @acrule(*(~~r, ~x::has_trig_exp) + *(~~r, ~y) => *(~~r..., ~x + ~y)),
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

const BOOLEAN_SIMPLIFIER = Chain(BOOLEAN_RULES)


function get_default_simplifier(; kw...)
    IfElse(has_trig_exp,
           Postwalk(IfElse(x->symtype(x) <: Number,
                           Chain((NUMBER_SIMPLIFIER, TRIG_EXP_SIMPLIFIER)),
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

threaded_simplifier(cutoff) = Fixpoint(get_default_simplifier(threaded=true,
                                                          thread_cutoff=cutoff))

const serial_expand_simplifier = If(iscall,
                                  Fixpoint(Chain((expand,
                                                  Fixpoint(get_default_simplifier())))))
