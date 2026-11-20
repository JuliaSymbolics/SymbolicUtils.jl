module AnyNumbers

    import Base: deepcopy_internal
    using DocStringExtensions: TYPEDSIGNATURES
    using SymbolicIndexingInterface: NotSymbolic, symbolic_type

    export AnyNumber

    # Single source of truth for the fast-path union. `ConcreteT`, the `isa` check
    # in `_wrap`, and the `@unionsplit` expansion all derive from this tuple, so
    # changing the member types means editing it only.
    const CONCRETE_TYPES = (Int, Float64, Rational{Int}, Complex{Int}, ComplexF64)
    const ConcreteT = Union{CONCRETE_TYPES...}

    struct AnyNumber <: Number
        concrete::ConcreteT
        is_concrete::Bool
        other::Number

        # `other` is left undefined on the concrete path: it is only ever read
        # when `is_concrete` is false, so pointing it at a sentinel would just
        # add a reference-field store (and a GC-visible pointer) to every
        # concrete allocation. The `Val` tags select the constructor — `true`
        # for the concrete path, `false` for `other` — and keep each call site
        # single-method so `max_methods=1` inference does not widen to `Any`.
        AnyNumber(x::ConcreteT, ::Val{true}) = new(x, true)
        function AnyNumber(x::Number, ::Val{false})
            (x isa ConcreteT || x isa AnyNumber) &&
                throw(ArgumentError("AnyNumber(x, Val(false)) requires a non-ConcreteT Number"))
            return new(0, false, x)
        end
    end

    # Shared boxes for small-`Int` results — `AnyNumber` is immutable, so the
    # common coefficients `-8:8` can be shared rather than re-allocated on every
    # operation or dictionary insertion. `===` on `Int` is type-exact, so
    # `Int8(1)`/`true` still allocate their own box and preserve `typeof`.
    const _SMALL_INTS = ntuple(i -> AnyNumber(i - 9, Val(true)), 17)
    const _ZERO = _SMALL_INTS[9]
    const _ONE = _SMALL_INTS[10]
    const _NEGONE = _SMALL_INTS[8]

    """
        $TYPEDSIGNATURES

    Wrap `x` in an `AnyNumber`, deriving `is_concrete` from `x`'s own type rather
    than from the inputs: concrete-path operations whose result leaves
    [`CONCRETE_TYPES`](@ref) (e.g. `Rational{Int} * Complex{Int}`) demote to `other`,
    and `other`-path results may re-enter the concrete path.

    `_wrap` must stay a single method: `SymbolicUtils` compiles with
    `max_methods=1`, so a call site whose argument admits more than one
    applicable `_wrap` signature infers `Any`. Idempotency for `AnyNumber` input
    is folded in rather than dispatched on.
    """
    @inline function _wrap(x::Number)
        if x isa ConcreteT
            x isa Int && -8 <= x <= 8 && return _SMALL_INTS[x + 9]
            return AnyNumber(x, Val(true))
        end
        x isa AnyNumber && return x
        return AnyNumber(x, Val(false))
    end
    AnyNumber(x::Number) = _wrap(x)
    # Resolves the ambiguity between `AnyNumber(::Number)` and
    # `(::Type{T})(::AnyNumber) where T<:Number`.
    AnyNumber(a::AnyNumber) = a

    """
        $TYPEDSIGNATURES

    The stored value with its static type erased to `Number`. Convenience for
    non-interface code (tests, debugging); interface methods never use it because
    dispatching on the result defeats both union-splitting and escape analysis.
    """
    @inline _value(a::AnyNumber) = a.is_concrete ? a.concrete : a.other

    _unreachable() = error("Unreachable reached.")

    # `if`/`elseif` chain over `CONCRETE_TYPES` with an `_unreachable()` tail. Julia
    # narrows `v` inside each branch via type-guard propagation, so this produces
    # optimized IR identical to the handwritten chain while deriving the branches
    # from `CONCRETE_TYPES`.
    function _unionsplit_chain(v, body)
        ex = :($_unreachable())
        for T in Iterators.reverse(CONCRETE_TYPES)
            ex = :(
                if $v isa $T
                    $body
                else
                    $ex
                end
            )
        end
        return ex
    end

    """
        $TYPEDSIGNATURES

    Evaluate `body` with `v` (a local bound to a `ConcreteT` value, typically
    `a.concrete`) manually union-split over each member of [`CONCRETE_TYPES`](@ref).
    Falls through to `_unreachable()` if `v` is not a member.
    """
    macro unionsplit(v::Symbol, body)
        return _unionsplit_chain(esc(v), esc(body))
    end

    # Builds the nested `is_concrete` dispatch tree for a call over `args`. Each
    # argument contributes `if a.is_concrete; v = a.concrete; ...; else <use
    # a.other> end`, and the concrete bindings are union-split *only* on the path
    # where every argument is concrete. A mixed `concrete × other` leaf
    # dynamic-dispatches anyway (the `.other` argument is `Number`-typed), so
    # splitting the concrete argument there would just duplicate the leaf for no
    # benefit. `make_call(env)` receives the resolved argument expressions (a
    # bound `v` on concrete paths, `a.other` otherwise) and returns the call
    # expression. `wrap` selects whether the result goes through `_wrap`
    # (arithmetic) or is returned raw (comparisons, predicates, `convert`).
    # `assert` optionally type-asserts the leaf call — needed on `.other` paths
    # where inference cannot prove e.g. `+(::Number, ::Int)` returns a `Number`,
    # and free on concrete leaves where it folds away.
    function _dispatch_tree(make_call, args::Tuple; wrap::Bool, assert = nothing)
        function rec(i, env, bound)
            if i > length(args)
                call = make_call(env)
                ex = assert === nothing ? call : Expr(:(::), call, assert)
                leaf = wrap ? :(_wrap($ex)) : ex
                if length(bound) == length(args)
                    for v in Iterators.reverse(bound)
                        leaf = _unionsplit_chain(v, leaf)
                    end
                end
                return leaf
            end
            a = args[i]
            v = gensym(Symbol(:v_, a))
            return quote
                if $a.is_concrete
                    $v = $a.concrete
                    $(rec(i + 1, Any[env; v], Any[bound; v]))
                else
                    $(rec(i + 1, Any[env; :($a.other)], bound))
                end
            end
        end
        return rec(1, Any[], Any[])
    end

    _call(f, env) = Expr(:call, GlobalRef(Base, f), env...)
    _call(f, env, pre, post) = Expr(:call, GlobalRef(Base, f), pre..., env..., post...)

    for f in (
            :+, :-, :*, :/, :\, ://, :^, :div, :fld, :cld, :mod, :rem, :mod1, :fld1,
            :gcd, :lcm, :invmod, :min, :max, :copysign, :flipsign, :atan, :atand,
            :hypot, :ldexp, :widemul, :binomial,
            :<<, :>>, :>>>, :&, :|, :xor,
        )
        tree = _dispatch_tree(
            env -> _call(f, env), (:a, :b);
            wrap = true, assert = Number
        )
        @eval function Base.$f(a::AnyNumber, b::AnyNumber)
            $tree
        end
    end

    # `div(x, y, r)` is the only 3-arg RoundingMode division form whose Base
    # signature is typed enough to extend without ambiguity (`rem(x, y, r)`
    # conflicts with Base's per-mode `rem(x, y, ::RoundingMode{:M})` methods).
    let tree = _dispatch_tree(
            env -> _call(:div, env, (), (:r,)), (:a, :b);
            wrap = true, assert = Number
        )
        @eval function Base.div(a::AnyNumber, b::AnyNumber, r::RoundingMode)
            $tree
        end
    end
    Base.div(a::AnyNumber, b::Number, r::RoundingMode) =
        _issymbolic(b) ? div(_value(a), b, r) : div(a, _wrap(b), r)
    Base.div(a::Number, b::AnyNumber, r::RoundingMode) =
        _issymbolic(a) ? div(a, _value(b), r) : div(_wrap(a), b, r)

    for f in (:(==), :<, :<=, :>, :>=, :isless, :isequal)
        tree = _dispatch_tree(
            env -> _call(f, env), (:a, :b);
            wrap = false, assert = Bool
        )
        @eval function Base.$f(a::AnyNumber, b::AnyNumber)
            $tree
        end
    end

    let tree = _dispatch_tree(
            env -> _call(:cmp, env), (:a, :b);
            wrap = false, assert = Int
        )
        @eval function Base.cmp(a::AnyNumber, b::AnyNumber)
            $tree
        end
    end

    for f in (:fma, :muladd, :clamp, :powermod, :hypot)
        tree = _dispatch_tree(
            env -> _call(f, env), (:a, :b, :c);
            wrap = true, assert = Number
        )
        @eval function Base.$f(a::AnyNumber, b::AnyNumber, c::AnyNumber)
            $tree
        end
    end

    for f in (
            :-, :+, :abs, :abs2, :sign, :conj, :adjoint, :float, :real, :imag,
            :angle, :inv, :exp, :exp2, :exp10, :expm1, :log, :log2, :log10, :log1p,
            :sqrt, :cbrt, :isqrt, :factorial,
            :sin, :cos, :tan, :sinh, :cosh, :tanh, :asin, :acos, :atan,
            :asinh, :acosh, :atanh,
            :sec, :csc, :cot, :sech, :csch, :coth, :asec, :acsc, :acot,
            :asech, :acsch, :acoth,
            :sind, :cosd, :tand, :secd, :cscd, :cotd,
            :asind, :acosd, :atand, :asecd, :acscd, :acotd,
            :cis, :cispi, :sinc, :cosc, :sinpi, :cospi, :tanpi,
            :deg2rad, :rad2deg, :mod2pi,
            :nextfloat, :prevfloat, :bswap, :bitreverse,
            :zero, :one, :oneunit, :eps, :widen, :big, :significand, :exponent,
        )
        tree = _dispatch_tree(
            env -> _call(f, env), (:a,);
            wrap = true, assert = Number
        )
        @eval function Base.$f(a::AnyNumber)
            $tree
        end
    end

    for f in (
            :iszero, :isone, :isinteger, :isreal, :isnan, :isinf, :isfinite,
            :isodd, :iseven, :signbit, :ispow2,
        )
        tree = _dispatch_tree(
            env -> _call(f, env), (:a,);
            wrap = false, assert = Bool
        )
        @eval function Base.$f(a::AnyNumber)
            $tree
        end
    end

    for f in (
            :count_ones, :count_zeros, :leading_ones, :leading_zeros,
            :trailing_ones, :trailing_zeros,
        )
        tree = _dispatch_tree(
            env -> _call(f, env), (:a,);
            wrap = false, assert = Int
        )
        @eval function Base.$f(a::AnyNumber)
            $tree
        end
    end

    # `rationalize` accepts a `tol` keyword.
    let tree = _dispatch_tree(
            env -> _call(
                :rationalize, env,
                (Expr(:parameters, Expr(:..., :kwargs)),), ()
            ),
            (:a,); wrap = true, assert = Number
        )
        @eval function Base.rationalize(a::AnyNumber; kwargs...)
            $tree
        end
    end

    # `hash` must agree with the wrapped value for `Dict`/hash-consing interop.
    function Base.hash(a::AnyNumber, h::UInt)
        a.is_concrete || return hash(a.other, h)::UInt
        v = a.concrete
        return @unionsplit v hash(v, h)
    end

    function Base.show(io::IO, a::AnyNumber)
        a.is_concrete || return show(io, a.other)
        v = a.concrete
        return @unionsplit v show(io, v)
    end

    Base.convert(::Type{AnyNumber}, a::AnyNumber) = a
    Base.convert(::Type{AnyNumber}, x::Number) = AnyNumber(x)

    # `other` is `#undef` on the concrete path, which the generic fieldwise
    # `deepcopy` would read. Concrete values are isbits, so they share safely;
    # `other` may hold a mutable number (e.g. `BigInt`) and is copied.
    deepcopy_internal(x::AnyNumber, dict::IdDict) =
        x.is_concrete ? x : AnyNumber(deepcopy_internal(x.other, dict), Val(false))

    # Type-targeted methods (`convert`, `T(a)`, `floor(T, a)`, `rationalize(T, a)`,
    # `round(T, a, r)`) enumerate literal types rather than catching all with
    # `where T<:Number`/`where T`: a generic `(::Type{T})(::AnyNumber)` is ambiguous
    # against a downstream `(::Type{MyNumber})(::Number)` — same for `convert` and
    # friends. Literal `::Type{X}` signatures can never overlap with methods on
    # types that don't exist yet; `Number` subtypes defined later fall through to
    # the generic convert/constructor path, like any other `Number`.
    const _CONVERT_TYPES = (
        Bool,
        Int8, Int16, Int32, Int64, Int128, BigInt,
        UInt8, UInt16, UInt32, UInt64, UInt128,
        Float16, Float32, Float64, BigFloat,
        Real, AbstractFloat, Integer, Signed, Unsigned, AbstractIrrational,
    )
    # `Rational`/`Complex`/`Irrational` are concrete union-alls — nothing can
    # subtype them — so `where` bounds on these are ambiguity-free, and binding `T`
    # preserves the requested parameter (`Rational{BigInt}`, `ComplexF64`; a literal
    # `::Type{Complex}` method would wrongly reduce `convert(ComplexF64, a)` to
    # `convert(Complex, v)` → `Complex{Int}`).
    const _SEALED_PARAM_TYPES = (:Rational, :Complex, :Irrational)
    for T in _CONVERT_TYPES
        tree = _dispatch_tree(
            env -> _call(:convert, env, (T,), ()), (:a,);
            wrap = false, assert = T
        )
        @eval function Base.convert(::Type{$T}, a::AnyNumber)
            $tree
        end
        @eval (::Type{$T})(a::AnyNumber) = convert($T, a)
    end
    for U in _SEALED_PARAM_TYPES
        tree = _dispatch_tree(
            env -> _call(:convert, env, (:T,), ()), (:a,);
            wrap = false, assert = :T
        )
        @eval function Base.convert(::Type{T}, a::AnyNumber) where {T <: $U}
            $tree
        end
        @eval (::Type{T})(a::AnyNumber) where {T <: $U} = convert(T, a)
    end

    # `rationalize(T, x)` returns `Rational{T}`, not `T` — Base only defines it for
    # `T<:Integer`, so it enumerates the integer members of `_CONVERT_TYPES`.
    for T in _CONVERT_TYPES
        T <: Integer || continue
        tree = _dispatch_tree(
            env -> _call(
                :rationalize, env,
                (Expr(:parameters, Expr(:..., :kwargs)), T), ()
            ),
            (:a,); wrap = false,
            assert = Expr(:curly, :Rational, T)
        )
        @eval function Base.rationalize(::Type{$T}, a::AnyNumber; kwargs...)
            $tree
        end
    end

    # AnyNumber is deliberately absorbing: mixed operations funnel through
    # promotion into the split binary methods.
    Base.promote_rule(::Type{AnyNumber}, ::Type{AnyNumber}) = AnyNumber
    Base.promote_rule(::Type{AnyNumber}, ::Type{<:Number}) = AnyNumber

    function Base.literal_pow(::typeof(^), a::AnyNumber, ::Val{p}) where {p}
        a.is_concrete ||
            return _wrap((Base.literal_pow(^, a.other, Val{p}()))::Number)
        v = a.concrete
        return @unionsplit v _wrap(Base.literal_pow(^, v, Val{p}()))
    end

    let tree = _dispatch_tree(
            env -> Expr(
                :call, GlobalRef(Base, :isapprox),
                Expr(:parameters, Expr(:..., :kws)), env...
            ),
            (:a, :b); wrap = false, assert = Bool
        )
        @eval function Base.isapprox(a::AnyNumber, b::AnyNumber; kws...)
            $tree
        end
    end

    for f in (:floor, :ceil, :trunc, :round)
        tree = _dispatch_tree(
            env -> _call(
                f, env,
                (Expr(:parameters, Expr(:..., :kwargs)),), ()
            ),
            (:a,); wrap = true, assert = Number
        )
        @eval function Base.$f(a::AnyNumber; kwargs...)
            $tree
        end

        for T in _CONVERT_TYPES
            tree = _dispatch_tree(
                env -> _call(
                    f, env,
                    (Expr(:parameters, Expr(:..., :kwargs)), T), ()
                ),
                (:a,); wrap = false, assert = T
            )
            @eval function Base.$f(::Type{$T}, a::AnyNumber; kwargs...)
                $tree
            end
        end
        for U in _SEALED_PARAM_TYPES
            tree = _dispatch_tree(
                env -> _call(
                    f, env,
                    (Expr(:parameters, Expr(:..., :kwargs)), :T), ()
                ),
                (:a,); wrap = false, assert = :T
            )
            @eval function Base.$f(::Type{T}, a::AnyNumber; kwargs...) where {T <: $U}
                $tree
            end
        end
    end

    # `round` is the only member of the rounding family taking a positional
    # `RoundingMode` — enumerated like the `(::Type{T}, a)` forms above. Union
    # types like `Union{Missing, Int}` reach missing.jl's generic, which forwards
    # into the literal `round(Int, a, r)` method and `convert`s back.
    for T in _CONVERT_TYPES
        tree = _dispatch_tree(
            env -> _call(:round, env, (T,), (:r,)),
            (:a,); wrap = false, assert = T
        )
        @eval function Base.round(::Type{$T}, a::AnyNumber, r::RoundingMode)
            $tree
        end
    end
    for U in _SEALED_PARAM_TYPES
        tree = _dispatch_tree(
            env -> _call(:round, env, (:T,), (:r,)),
            (:a,); wrap = false, assert = :T
        )
        @eval function Base.round(::Type{T}, a::AnyNumber, r::RoundingMode) where {T <: $U}
            $tree
        end
    end

    let tree = _dispatch_tree(
            env -> _call(:round, env, (), (:r,)),
            (:a,); wrap = true, assert = Number
        )
        @eval function Base.round(a::AnyNumber, r::RoundingMode)
            $tree
        end
    end

    let tree = _dispatch_tree(
            env -> _call(:rem2pi, env, (), (:r,)), (:a,);
            wrap = true, assert = Number
        )
        @eval function Base.rem2pi(a::AnyNumber, r::RoundingMode)
            $tree
        end
    end

    Base.zero(::Type{AnyNumber}) = AnyNumber(0)
    Base.one(::Type{AnyNumber}) = AnyNumber(1)
    Base.oneunit(::Type{AnyNumber}) = AnyNumber(1)
    Base.float(::Type{AnyNumber}) = AnyNumber
    Base.widen(::Type{AnyNumber}) = AnyNumber

    # Mixed-signature forwards. Several Base fallbacks dispatch on `Real` pairs
    # (`min`, `isless`, `cmp`) or don't promote at all (bitwise ops, `//`), so every
    # binary op gets forwards that wrap the plain argument and re-dispatch to the
    # split `AnyNumber`/`AnyNumber` method. A `Number` argument that is symbolic
    # (`Num`, `BasicSymbolic` wrappers, `symbolic_type != NotSymbolic()`) is never
    # wrapped: the operation belongs to the symbolic's own methods, so the
    # `AnyNumber` is unwrapped instead and the result stays symbolic. The check
    # dispatches on the argument's type and folds to `false` for plain numbers.
    @inline _issymbolic(@nospecialize(x)) = symbolic_type(x) !== NotSymbolic()
    @inline _rawarg(x) = x
    @inline _rawarg(a::AnyNumber) = _value(a)

    # Only ops that are meaningful for every `CONCRETE_TYPES` member or are
    # registered symbolic functions (`diadic` in `methods.jl`, `binomial`) get
    # mixed forwards: bitwise/number-theoretic ops cannot apply to
    # `Float64`/`Rational`/`Complex` contents, and each forward is also an
    # ambiguity source against downstream `f(::Number, ::SymbolicNumber)`.
    for f in (
            :+, :-, :*, :/, :\, :div, :fld, :cld, :mod, :rem,
            :gcd, :lcm, :min, :max, :copysign, :atan,
            :hypot, :widemul, :binomial,
            :(==), :<, :<=, :>, :>=, :isless, :isequal, :cmp,
        )
        @eval Base.$f(a::AnyNumber, b::Number) =
            _issymbolic(b) ? $f(_value(a), b) : $f(a, _wrap(b))
        @eval Base.$f(a::Number, b::AnyNumber) =
            _issymbolic(a) ? $f(a, _value(b)) : $f(_wrap(a), b)
    end

    # `//` is restricted to `Real` to avoid ambiguities with `//(::Complex, ::Real)`
    # and `//(::Number, ::Complex)` — `AnyNumber` is never `Complex`. Base's
    # `//(::Number, ::Complex)` still handles a complex denominator.
    Base.://(a::AnyNumber, b::Real) =
        _issymbolic(b) ? _value(a) // b : a // _wrap(b)
    Base.://(a::Real, b::AnyNumber) =
        _issymbolic(a) ? a // _value(b) : _wrap(a) // b

    # `^` needs an `Integer`-bound method to stay more specific than Base's
    # `^(::Number, ::Integer)` for `a^n`.
    Base.:^(a::AnyNumber, b::Integer) = ^(a, _wrap(b))
    Base.:^(a::AnyNumber, b::Number) =
        _issymbolic(b) ? _value(a) ^ b : ^(a, _wrap(b))
    Base.:^(a::Number, b::AnyNumber) =
        _issymbolic(a) ? a ^ _value(b) : ^(_wrap(a), b)

    Base.isapprox(a::AnyNumber, b::Number; kws...) =
        _issymbolic(b) ? isapprox(_value(a), b; kws...) : isapprox(a, _wrap(b); kws...)
    Base.isapprox(a::Number, b::AnyNumber; kws...) =
        _issymbolic(a) ? isapprox(a, _value(b); kws...) : isapprox(_wrap(a), b; kws...)

    # Disambiguations against more specific Base methods.
    Base.widemul(a::AnyNumber, b::Bool) = widemul(a, _wrap(b))
    Base.widemul(a::Bool, b::AnyNumber) = widemul(_wrap(a), b)
    Base.:^(a::AnyNumber, b::Rational) = ^(a, _wrap(b))
    Base.:^(a::Irrational{:ℯ}, b::AnyNumber) = ^(_wrap(a), b)
    Base.binomial(a::AnyNumber, b::Integer) = binomial(a, _wrap(b))

    # `clamp` may return `lo`/`hi` unchanged, so mixed signatures must wrap them
    # too rather than falling back to the unpromoting Base generic.
    for (X, Y, Z) in (
                (AnyNumber, Number, Number), (Number, AnyNumber, Number),
                (Number, Number, AnyNumber), (AnyNumber, AnyNumber, Number),
                (AnyNumber, Number, AnyNumber), (Number, AnyNumber, AnyNumber),
            ),
            f in (:clamp, :fma, :muladd)
        @eval function Base.$f(x::$X, y::$Y, z::$Z)
            if _issymbolic(x) || _issymbolic(y) || _issymbolic(z)
                return $f(_rawarg(x), _rawarg(y), _rawarg(z))
            end
            return $f(_wrap(x), _wrap(y), _wrap(z))
        end
    end

    include("anydict.jl")

    """
        AnyNumber <: Number

    Developer-facing `Number` wrapper —

        struct AnyNumber <: Number
            concrete::ConcreteT
            is_concrete::Bool
            other::Number
        end

    a `Number` backed by either a small isbits union (`concrete`) or an arbitrary
    `Number` (`other`), selected by `is_concrete`. Every operation checks
    `is_concrete` first and manually union-splits the concrete value through
    `@unionsplit`, avoiding dynamic dispatch and letting escape analysis
    elide the wrapper. Results are passed through `_wrap`, which
    re-derives the flag from the result type: concrete-path operations whose
    result leaves `CONCRETE_TYPES` (e.g. `Rational{Int} * Complex{Int}`)
    demote to `other`, and `other`-path results may re-enter the concrete path.
    Functions returning tuples (`frexp`, `modf`, `divrem`, `minmax`, `sincos`,
    ...) are intentionally unsupported.
    """
    AnyNumber

end # module AnyNumbers
