# Variant structure and types

This document aims to describe the structure of the Algebraic Data Type (ADT) used to represent
a symbolic tree, along with several utility types to allow robustly interacting with it.

SymbolicUtils uses Moshi.jl's ADT structure. The ADT is named `BasicSymbolicImpl`, and an alias
`BSImpl` is available for convenience. The actual type of a variable is `BSImpl.Type`, aliased
as `BasicSymbolic`. A `BasicSymbolic` is considered immutable. Mutating its fields is unsafe
behavior.

In SymbolicUtils v3, the type `T` in `BasicSymbolic{T}` was the type represented by the symbolic
variable. In other words, `T` was the [`SymbolicUtils.symtype`](@ref) of the variable.

In SymbolicUtils v4, the `symtype` is not stored in the type, and is instead a field of the
struct. This allows for greatly increased type-stability. The type `T` in `BasicSymbolic{T}`
now represents a tag known as the [`vartype`](@ref). This flag determines the assumptions
made about the symbolic algebra. It can take one of three values:

- [`SymReal`](@ref): The default behavior.
- [`SafeReal`](@ref): Identical to `SymReal`, but common factors in the numerator and denominator
  of a division are not cancelled.
- [`TreeReal`](@ref): Assumes nothing about the algebra, and always uses the `Term` variant to
  represent an expression.

A given expression must be pure in its `vartype`. In other words, no operation supports operands
of different `vartype`s.

!!! warning "A short note on (im-)mutability"
  
    While `ismutabletype(BasicSymbolic)` returns `true`, symbolic types are IMMUTABLE.
    Any mutation is undefined behavior and can lead to very confusing and hard-to-debug issues.
    This includes internal mutation, such as mutating `AddMul.dict`. The arrays returned from
    `TermInterface.arguments` and `TermInterface.sorted_arguments` are read-only arrays for this
    reason.

## Expression symtypes

The "symtype" of a symbolic variable/expression is the Julia type that the variable/expression
represents. It can be queried with [`SymbolicUtils.symtype`](@ref). Note that this query is
unstable - the returned type cannot be inferred.

## Expression shapes

In SymbolicUtils v4, arrays are first-class citizens. This is implemented by storing the shape
of the symbolic. The shape can be queried using [`SymbolicUtils.shape`](@ref) and is one of
two types.

### Symbolics with known shape

The most common case is when the shape of a symbolic variable is known. For example:

```julia
@syms x[1:2] y[-3:6, 4:7] z
```

All of the variables created above have known shape. In this case, `SymbolicUtils.shape`
returns a (custom) vector of `UnitRange{Int}` semantically equivalent to `Base.axes`. This
does not return a `Tuple` since the number of dimensions cannot be inferred and thus
returning a tuple would introduce type-instability. All array operations will perform
validation on the shapes of their inputs (e.g. matrix multiplication) and calculates the
shape of their outputs.

Scalar variables return an empty vector as their shape.

### Symbolics with known `ndims`

The next most common case is when the exact shape/size of the symbolic is unknown but the
number of dimensions is known. For example:

```julia
@syms x::Vector{Number} y::Matrix{Number} z::Array{Number, 3}
```

In this case, `SymbolicUtils.shape` returns a value of type [`SymbolicUtils.Unknown`](@ref).
This has a single field `ndims::Int` storing the number of dimensions of the symbolic. Note
that a shape of `SymbolicUtils.Unknown(0)` does not represent a scalar. All array operations
will perform as much validation as possible on their arguments. The shape of the result will
be calculated on a best-effort basis.

### Symbolics with unknown `ndims`

In this case, nothing is known about the symbolic except that it is an array. For example:

```julia
@syms x::Array{Number}
```

`Symbolics.shape(x)` will return `SymbolicUtils.Unknown(-1)`. This effectively disables most
shape checking for array operations.

## Variants

```julia
struct Const
    const val::Any
    # ...
end
```

Any non-symbolic values in an expression are stored in a `Const` variant. This is crucial for
type-stability, but it does mean that obtaining the value out of a `Const` is unstable and
should be avoided. This value can be obtained by pattern matching using `Moshi.Match.@match`
or using the [`unwrap_const`](@ref) utility. `unwrap_const` will act as an identity function
for any input that is not `Const`, including non-symbolic inputs. `Const` is the only variant
which does not have metadata.

[`SymbolicUtils.isconst`](@ref) can be used to check if a `BasicSymbolic` is the `Const`
variant. This variant can be constructed using `Const{T}(val)` or `BSImpl.Const{T}(val)`,
where `T` is the appropriate `vartype`.

The `Const` constructors have an additional special behavior. If given an array of symbolics
(or array of array of ... symbolics), it will return a `Term` (see below) with
[`SymbolicUtils.array_literal`](@ref) as the operation. This allows standard symbolic
operations (such as [`substitute`](@ref)) to work on arrays of symbolics without excessive
special-case handling and improved type-stability.

```julia
struct Sym
    const name::Symbol
    const metadata::MetadataT
    const shape::ShapeT
    const type::TypeT
    # ...
end
```

`Sym` represents a symbolic quantity with a given `name`. This and `Const` are the two atomic
variants. `metadata` is the symbolic metadata associated with this variable. `type` is the
tag for the type of quantity represented here. `shape` stores the shape if the variable is
an array symbolic.

- `metadata` is either `nothing` or a map from `DataType` keys to arbitrary values. Any
  interaction with metadata should be done by providing such a mapping during construction
  or using [`getmetadata`](@ref), [`setmetadata`](@ref), [`hasmetadata`](@ref).
- `type` is a Julia type.
- `shape` is as described above.

These three fields are present in all subsequent variants as well.

A `Sym` can be constructed using `Sym{T}(name::Symbol; type, shape, metadata)` or
`BSImpl.Sym{T}(name::Symbol; type, shape, metadata)`.

```julia
struct Term
    const f::Any
    const args::SmallV{BasicSymbolicImpl.Type{T}}
    const metadata::MetadataT
    const shape::ShapeT
    const type::TypeT
    # ...
end
```

`Term` is the generic expression form for an operation `f` applied to the arguments in
`args`. In other words, this represents `f(args...)`. Any constant (non-symbolic) arguments
(including arrays of symbolics) are converted to symbolics and wrapped in `Const`.

A `Term` can be constructed using `Term{T}(f, args; type, shape, metadata)` or
`BSImpl.Term{T}(f, args; type, shape, metadata)`.

```julia
struct AddMul
    const coeff::Any
    const dict::ACDict{T}
    const variant::AddMulVariant.T
    const metadata::MetadataT
    const shape::ShapeT
    const type::TypeT
    # ...
end
```

`AddMul` is a specialized representation for associative-commutative addition and
multiplication. The two operations are distinguished using the [`AddMulVariant`](@ref)
EnumX.jl enum. It has two variants: `AddMulVariant.ADD` and `AddMulVariant.MUL`.

For multiplication terms, `coeff` is a constant non-symbolic coefficient multiplied
with the expression. `dict` is a map from terms being multiplied to their exponents. For
example, `2x^2 * (y + z)^3` is represented with `coeff = 2` and
`dict = ACDict{T}(x => 2, (y + z) => 3)`. A valid multiplication term is subject to the
following constraints:

- `coeff` must be non-symbolic.
- The values of `dict` must be non-symbolic.
- The keys of `dict` must not be expressions with `^` as the operation UNLESS the exponent
  is symbolic. For example, `x^x * y^2` is represented with
  `dict = ACDict{T}((x^x) => 1, y => 2)`.
- `dict` must not be empty.
- `coeff` must not be zero.
- If `dict` has only one element, `coeff` must not be one. Such a case should be
  represented as a power term (with `^` as the operation).
- If `dict` has only one element where the key is an addition, `coeff` must not be negative
  one. Such a case should be represented by distributing the negation.

The `Mul{T}(coeff, dict; type, shape, metadata)` constructor validates these constraints
and automatically returns the appropriate alternative form where applicable. It should
be preferred. `BSImpl.AddMul{T}(coeff, dict, variant; type, shape, metadata)` is
faster but does not validate the constraints and should be used with caution. Incorrect
usage can and will lead to both invalid expressions and undefined behavior.

For addition terms, `coeff` is a constant non-symbolic coefficient added to the
expression. `dict` is a map from terms being added to the constant non-symbolic
coefficients they are multiplied by. For example, to represent `1 + 2x + 3y * z`
`coeff` would be `1` and `dict` would be `Dict(x => 2, (y * z) => 3)`. A valid addition
term is subject to the following constraints:

- `coeff` must be non-symbolic.
- The values of `dict` must be non-symbolic.
- The keys of `dict` must not be additions expressions represented with `AddMul`.
- `dict` must not be empty.
- If `dict` has only one element, `coeff` must not be zero. Such a case should be
  represented using the appropriate multiplication form.

The `Add{T}(coeff, dict; type, shape, metadata)` constructor validates these constraints
and automatically returns the appropriate alternative form where applicable. It should
be preferred. `BSImpl.AddMul{T}(coeff, dict, variant; type, shape, metadata)` is
faster but does not validate the constraints and should be used with caution. Incorrect
usage can and will lead to both invalid expressions and undefined behavior.

```julia
struct Div
    const num::BasicSymbolicImpl.Type{T}
    const den::BasicSymbolicImpl.Type{T}
    const simplified::Bool
    const metadata::MetadataT
    const shape::ShapeT
    const type::TypeT
    # ...
end
```

The `Div` variant represents division (where the operation is `/`). `num` is the numerator
and `den` is the denominator expression. `simplified` is a boolean indicating whether this
expression is in the most simplified form possible. If it is `true`, certain algorithms in
[`simplify_fractions`](@ref) will not inspect this term. In almost all cases, it should be
provided as `false`. A valid division term is subject to the following constraints:

- Both the numerator and denominator cannot be `Const` variants. This should instead be
  represented as a `Const` variant wrapping the result of division.
- The numerator cannot be zero. This should instead be represented as a `Const` wrapping
  the appropriate zero.
- The denominator cannot be one. This should instead be represented as the numerator,
  possibly wrapped in a `Const`.
- The denominator cannot be zero. This should instead be represented as a `Const` with
  some form of infinity.
- The denominator cannot be negative one. This should instead be represented as the negation
  of the numerator.
- Non-symbolic coefficients should be propagated to the numerator if it is a constant or
  multiplication term.

The `Div{T}(num, den, simplified; type, shape, metadata)` constructor can be used to build
this form. If `T` is `SymReal`, the constructor will use [`quick_cancel`](@ref) to cancel
trivially identifiable common factors in the numerator and denominator. It will also perform
validation of the above constraints and return the appropriate alternative form where
applicable. Some of the constraints can be relaxed for non-scalar algebras. The
`BSImpl.Div{T}(num, den, simplified; type, shape, metadata)` does not perform such
validation or transformation.

```julia
struct ArrayOp
    const output_idx::SmallV{Union{Int, BasicSymbolicImpl.Type{T}}}
    const expr::BasicSymbolicImpl.Type{T}
    const reduce::Any
    const term::Union{BasicSymbolicImpl.Type{T}, Nothing}
    const ranges::Dict{BasicSymbolicImpl.Type{T}, StepRange{Int, Int}}
    const metadata::MetadataT
    const shape::ShapeT
    const type::TypeT
    # ...
end
```

`ArrayOp` is used to represent vectorized operations. This variant should not be created
manually. Instead, the [`@arrayop`](@ref) macro constructs this using a generalized
Einstein-summation notation, similar to that of Tullio.jl. Consider the following example:

```julia
ex = @arrayop (i, j) A[i, k] * B[k, j] + C[i, j]
```

This represents `A * B + C` for matrices `A, B, C` as a vectorized array operation. Some
operations, such as broadcasts, are automatically represented as such a form internally.
The following description of the fields assumes familiarity with the `@arrayop` macro.

When processing this macro, the indices `i, j, k` are converted to use a common global
index variable to avoid potential name conflicts with other symbolic variables named
`i, j, k` if `ex` is used in a larger expression. The `output_idx` field stores `[i, j]`.
`expr` stores the expression `A[i, k] * B[k, j] + C[i, j]`, with `i, j, k` replaced by the
common global index variable. `reduce` is the operation used to reduce indices not present
in `output_idx` (in this example, `k`). By default, it is `+`. `term` stores an expression
that represents an equivalent computation to use for printing/code-generation. For example,
here `A * B + C` would be a valid value for `term`. By default, `term` is `nothing` except
when the expression is generated via `broadcast` or a similar operation. `ranges` is a
dictionary mapping indices used in `expr` (converted to the common global index) to the
range of indices over which they should iterate, in case such a range is explicitly
provided.

!!! note
  
  The common global index variable is printed as `_1`, `_2`, ... in arrayops. It is not
  a valid symbolic variable outside of an `ArrayOp`'s `expr`.

A valid `ArrayOp` satisfies the following conditions:

- `output_idx` only contains the integer `1` or variants of the common global index
  variable.
- Any top-level indexing operations in `expr` use common global indices. A top-level
  indexing operation is a term whose operation is `getindex`, and which is not a
  descendant of any other term whose operation is `getindex`.
- `reduce` must be a valid reduction operation that can be passed to `Base.reduce`.
- If `term` is not `nothing`, it must be an expression with shape `shape` and type `type`.
- The keys of `ranges` must be variants of the common global index variable, and must
  be present in `expr`.

The `@arrayop` macro should be heavily preferred for creating `ArrayOp`s. In case this is
not possible (such as in recursive functions like `substitute`) the `ArrayOp` constructor
should be preferred. This does not allow specifying the `type` and `shape`, since these
values are tied to the fields of the variant and are thus determined. The `BSImpl.ArrayOp`
constructor should be used with extreme caution, since it does not validate input.

```julia
struct ArrayMaker
    const regions::SmallV{ShapeVecT}
    const values::SmallV{BasicSymbolicImpl.Type{T}}
    const metadata::MetadataT
    const shape::ShapeT
    const type::TypeT
    # ...
end
```

`ArrayMaker` is used to represent symbolic arrays composed of (potentially overlapping)
blocks of other arrays. It is represented as a sequence `regions` of subarrays of the result,
and a corresponding sequence `values` of values assigned to them. Each entry in `regions`
must have the same number of dimensions as the represented array; singleton dimensions
cannot be removed. The corresponding entry in `values` must have a size identical to
the assigned subarray. Again, singleton dimensions cannot be dropped. In case of overlaps,
later entries overwrite earlier ones. If a region of the array is left unassigned by all
blocks, accessing it is invalid. When used in code generation, these unassigned regions
can take arbitrary and possibly unassigned values.

In most cases, `ArrayMaker` should not be created directly. Prefer using [`@makearray`](@ref).

## Array arithmetic

SymbolicUtils implements a simple array algebra in addition to the default scalar algebra.
Similar to how [`SymbolicUtils.promote_symtype`](@ref) given a function and symtypes of
its arguments returns the symtype of the result, [`SymbolicUtils.promote_shape`](@ref)
does the same for the shapes of the arguments. Implementing _both_ methods is crucial
for correctly using custom functions in symbolic expressions. Without `promote_shape`,
SymbolicUtils will use `Unknown(-1)` as the shape.

The array algebra implemented aims to mimic that of base `Array`s as closely as possible.
For example, a symbolic `adjoint(::Vector) * (::Vector)` will return a symbolic scalar
instead of a one-element symbolic vector. `promote_shape` implementations will
propagate the shape information on a best-effort basis. Invalid shapes (such as
attempting to multiply a 3-dimensional array) will error. Following are notable exceptions
to Base-like behavior:

- `map` and `mapreduce` require that all input arrays have the same `shape`
- `promote_symtype` and `promote_shape` is not implemented for `map` and `mapreduce`, since
  doing so requires the function(s) passed to `map` and `mapreduce` instead of their types
  or shapes.
- Since `ndims` information is not present in the type, `eachindex`, `iterate`, `size`,
  `axes`, `ndims`, `collect` are type-unstable. [`SymbolicUtils.stable_eachindex`](@ref) is
  useful as a type-stable iteration alternative.
- `ifelse` requires that both the true and false cases have identical shape.
- Symbolic arrays _only_ support Cartesian indexing. For example, given `@syms x[1:3, 1:3]`
  accessing `x[4]` is invalid and `x[1, 2]` should be used. Valid indices are
  `Int`, `Colon`, `AbstractRange{Int}` and symbolic expressions with integer `symtype`.
  A single `CartesianIndex` of appropriate dimension can also be used to symbolically
  index arrays.

Symbolic array operations are also supported on arrays of symbolics. However, at least one
of the arguments to the function must be a symbolic (instead of an array of symbolics) to
allow the dispatches defined in SymbolicUtils to be targeted instead of those in Base. To
aid in constructing arrays of symbolics, the [`BS`](@ref) utility is provided. Similar to
the `T[...]` syntax for constructing an array of etype `T`, `BS[...]` will construct an
array of `BasicSymbolic`s. At least one value in the array must be a symbolic value to
infer `T` in `Array{BasicSymbolic{T}, N}`. To explicitly specify the `vartype`, use
`BS{T}[...]`.

## Symbolic functions and dependent variables

SymbolicUtils defines `FnType{A, R, T}` for symbolic functions and dependent variables.
Here, `A` is a `Tuple{...}` of the symtypes of arguments and `R` is the type returned by
the symbolic function. `T` is the type that the function itself subtypes, or `Nothing`.

The syntax

```julia
@syms f(::T1, ::T2)::R
```

creates `f` with a symtype of `FnType{Tuple{T1, T2}, R, Nothing}`. This is a symbolic
function taking arguments of type `T1` and `T2`, and returning `R`. `Nothing` is a
sentinel indicating that the supertype of the function is unknown. By contrast,

```julia
@syms f(..)::R
```

creates `f` with a symtype of `FnType{Tuple, R, Nothing}`. SymbolicUtils considers this
case to be a dependent variable with as-yet unspecified independent variables. In other
words,

```julia
@syms x f1(::Real)::Real f2(..)::Real
```

Here, `f1(x)` is considered a symbolic function `f1` called with the argument `x` and
`f2(x)` is considered a dependent variable that depends on `x`. The utilities
[`SymbolicUtils.is_function_symbolic`](@ref), [`SymbolicUtils.is_function_symtype`](@ref),
[`SymbolicUtils.is_called_function_symbolic`](@ref) can be used to differentiate between
these cases.

## API

### Basics

```@docs
SymbolicUtils.BasicSymbolic
@syms
SymbolicUtils.symtype
SymbolicUtils.vartype
SymReal
SafeReal
TreeReal
SymbolicUtils.shape
SymbolicUtils.Unknown
SymbolicUtils.AddMulVariant
unwrap_const
```

### Inner constructors

```@docs
SymbolicUtils.array_literal
SymbolicUtils.BSImpl.Const
SymbolicUtils.BSImpl.Sym
SymbolicUtils.BSImpl.Term
SymbolicUtils.BSImpl.AddMul
SymbolicUtils.BSImpl.Div
SymbolicUtils.BSImpl.ArrayOp
SymbolicUtils.BSImpl.ArrayMaker
```

### High-level constructors

```@docs
SymbolicUtils.Const
SymbolicUtils.Sym
SymbolicUtils.Term
SymbolicUtils.Add
SymbolicUtils.Mul
SymbolicUtils.Div
SymbolicUtils.ArrayOp
@arrayop
SymbolicUtils.ArrayMaker
@makearray
```

### Variant checking

Note that while these utilities are useful, prefer using `Moshi.Match.@match` to pattern
match against different variant types and access their fields.

```@docs
SymbolicUtils.isconst
SymbolicUtils.issym
SymbolicUtils.isterm
SymbolicUtils.isaddmul
SymbolicUtils.isadd
SymbolicUtils.ismul
SymbolicUtils.isdiv
SymbolicUtils.ispow
SymbolicUtils.isarrayop
SymbolicUtils.isarraymaker
```

### Using custom functions in expressions

```@docs
SymbolicUtils.promote_symtype
SymbolicUtils.promote_shape
```

### Symbolic array utilities

```@docs
SymbolicUtils.stable_eachindex
SymbolicUtils.StableIndices
SymbolicUtils.StableIndex
SymbolicUtils.as_linear_idx
BS
```

### Symbolic function utilities

```@docs
SymbolicUtils.is_function_symbolic
SymbolicUtils.is_function_symtype
SymbolicUtils.is_called_function_symbolic
```

### TermInterface.jl interface

```@docs
TermInterface.iscall
TermInterface.operation
TermInterface.arguments
TermInterface.sorted_arguments
TermInterface.maketerm
```

### Miscellaneous utilities

```@docs
SymbolicUtils.zero_of_vartype
SymbolicUtils.one_of_vartype
SymbolicUtils.get_mul_coefficient
SymbolicUtils.term
SymbolicUtils.add_worker
SymbolicUtils.mul_worker
```

### Utility types

SymbolicUtils exposes a plethora of type aliases to allow easily interacting with common
types used internally.

```@docs
SymbolicUtils.MetadataT
SymbolicUtils.SmallV
SymbolicUtils.ShapeVecT
SymbolicUtils.ShapeT
SymbolicUtils.TypeT
SymbolicUtils.ArgsT
SymbolicUtils.ROArgsT
SymbolicUtils.ACDict
SymbolicUtils.OutIdxT
SymbolicUtils.RangesT
```
