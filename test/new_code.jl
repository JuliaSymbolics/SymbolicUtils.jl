using SymbolicUtils, NaNMath
using SymbolicUtils.Code
using Test
using StaticArrays
using LabelledArrays
using SparseArrays
using ReverseDiff
using LinearAlgebra

using SymbolicUtils: Const
import SymbolicUtils: replace_node!
using Moshi.Match: @match
import SymbolicUtils.BasicSymbolicImpl as BSImpl

test_repr(a, b) = @test repr(Base.remove_linenums!(a)) == repr(Base.remove_linenums!(b))

@testset "Code" begin
    @syms a b c d e p q t x(t) y(t) z(t)
    ir = IRStructure{SymReal}()
    test_repr(
        Code.fast_toexpr(Let([], Assignment(a, b)), ir, Dict()),
        :(
            let
                var"##cse#0" = b
                a = var"##cse#0"
            end
        )
    )
    test_repr(
        Code.fast_toexpr(a + b, ir, Dict()),
        quote
            var"##cse#0" = a
            var"##cse#1" = b
            var"##cse#2" = $(+)(var"##cse#0", var"##cse#1")
        end
    )
    test_repr(
        Code.fast_toexpr(a * b * c * d * e, ir, Dict()),
        quote
            var"##cse#0" = a
            var"##cse#1" = b
            var"##cse#2" = c
            var"##cse#3" = d
            var"##cse#4" = e
            var"##cse#5" = $(*)(var"##cse#0", var"##cse#1", var"##cse#2", var"##cse#3", var"##cse#4")
        end
    )
    newsym = eval(
        quote
            let x = $x, y = $y, t = $t
                $(Code.fast_toexpr(x(t) + y(t), ir, Dict()))
            end
        end
    )
    @test operation(newsym) === (+) && issetequal(arguments(newsym), [x(t), y(t)])
    newsym = eval(
        quote
            let x = $x, y = $y, t = $t
                $(Code.fast_toexpr(x(t) + y(t) + x(t + 1), ir, Dict()))
            end
        end
    )
    @test operation(newsym) === (+) && issetequal(arguments(newsym), [x(t), y(t), x(1 + t)])

    test_repr(
        Code.fast_toexpr(Let([a ← 3, b ← 1 + a], a + b), ir, Dict()),
        :(
            let __miscₛᵧₘ0 = 3, a = __miscₛᵧₘ0, var"##cse#0" = 1, var"##cse#1" = a,
                    var"##cse#2" = $(+)(var"##cse#0", var"##cse#1"), b = var"##cse#2"
                var"##cse#0" = a
                var"##cse#1" = b
                var"##cse#2" = $(+)(var"##cse#0", var"##cse#1")
            end
        )
    )
    newsym = eval(Code.fast_toexpr(Let([a ← 3, b ← 1 + a], a + b), ir, Dict()))
    @test isequal(newsym, 7)

    test_repr(
        Code.fast_toexpr(Func([], [], a + b), ir, Dict()),
        :(
            function ()
                begin
                    var"##cse#0" = a
                    var"##cse#1" = b
                    var"##cse#2" = $(+)(var"##cse#0", var"##cse#1")
                end
            end
        )
    )

    newf = eval(
        Code.fast_toexpr(
            Func([x(t), x, a, t], [b ← a + 2, y(t) ← b], x(t) + x(t + 1) + b + y(t)), ir, Dict()
        )
    )
    newsym = newf(x(t), x, a, t; var"y(t)" = y(t))
    @test operation(newsym) === (+) && issetequal(arguments(newsym), [x(t), x(1 + t), a, y(t), Const{SymReal}(2)])

    fexpr1 = Code.fast_toexpr(
        Func(
            [
                DestructuredArgs([x, x(t), t], :state),
                DestructuredArgs((a, b), :params),
            ], [],
            x(t + 1) + x(t) + a + b
        ), ir, Dict()
    )
    newf = eval(fexpr1)
    newsym = newf([x, x(t), t], [a, b])
    @test operation(newsym) === (+) && issetequal(arguments(newsym), [x(t + 1), x(t), a, b])

    fexpr2 = Code.fast_toexpr(
        Func(
            [
                DestructuredArgs([x, x(t), t], :state, create_bindings = false),
                DestructuredArgs((a, b), :params, create_bindings = false),
            ], [],
            x(t + 1) + x(t) + a + b
        ), ir, Dict()
    )
    newf = eval(fexpr2)
    newsym = newf([x, x(t), t], [a, b])
    @test operation(newsym) === (+) && issetequal(arguments(newsym), [x(t + 1), x(t), a, b])
    @test fexpr1 != fexpr2

    fexpr = Code.fast_toexpr(Func([], [], :(rand()), [Expr(:meta, :inline)]), ir, Dict())
    @test any(isequal(Expr(:meta, :inline)), fexpr.args[2].args)

    ex = Code.fast_toexpr(Func([DestructuredArgs([x, x(t)], :state, inbounds = true)], [], x(t + 1) + x(t)), ir, Dict())
    ex = Base.remove_linenums!(ex)
    for e in ex.args[2].args[1].args[[1, 3]]
        @test e.args[2].head == :macrocall
    end

    test_repr(
        Code.fast_toexpr(Let([], SetArray(false, a, [x(t), AtIndex(9, b), AtIndex(10, d), c])), ir, Dict()),
        :(
            let
                var"##cse#0" = a
                var"##cse#1" = x
                var"##cse#2" = t
                var"##cse#3" = var"##cse#1"(var"##cse#2")
                __miscₛᵧₘ0 = 9
                var"##cse#4" = b
                __miscₛᵧₘ1 = 10
                var"##cse#5" = d
                var"##cse#6" = c
                __miscₛᵧₘ3 = begin
                    var"##cse#0"[1] = var"##cse#3"
                    var"##cse#0"[__miscₛᵧₘ0] = var"##cse#4"
                    var"##cse#0"[__miscₛᵧₘ1] = var"##cse#5"
                    var"##cse#0"[4] = var"##cse#6"
                    __miscₛᵧₘ2 = nothing
                end
            end
        )
    )
    @test Code.fast_toexpr(SetArray(true, a, [x(t), AtIndex(9, b), c]), ir, Dict()).head == :macrocall

    for fname in (:sin, :cos, :tan, :asin, :acos, :acosh, :atanh, :log, :log2, :log10, :log1p, :sqrt)
        f = getproperty(Base, fname)
        test_repr(
            Code.fast_toexpr(f(a), ir, Dict()), quote
                var"##cse#0" = a
                var"##cse#1" = $(f)(var"##cse#0")
            end
        )
        test_repr(
            Code.fast_toexpr(f(a), ir, Dict{Any, Any}(:nanmath => true)), quote
                var"##cse#0" = a
                var"##cse#1" = $(GlobalRef(NaNMath, fname))(var"##cse#0")
            end
        )

        nanmath_f = getproperty(NaNMath, fname)
        test_repr(
            Code.fast_toexpr(nanmath_f(a), ir, Dict()), quote
                var"##cse#0" = a
                var"##cse#1" = $nanmath_f(var"##cse#0")
            end
        )
        test_repr(
            Code.fast_toexpr(nanmath_f(a), ir, Dict{Any, Any}(:nanmath => true)), quote
                var"##cse#0" = a
                var"##cse#1" = $nanmath_f(var"##cse#0")
            end
        )
    end

    test_repr(
        Code.fast_toexpr(a^b, ir, Dict()), quote
            var"##cse#0" = a
            var"##cse#1" = b
            var"##cse#2" = $(^)(var"##cse#0", var"##cse#1")
        end
    )
    test_repr(
        Code.fast_toexpr(a^b, ir, Dict{Any, Any}(:nanmath => true)), quote
            var"##cse#0" = a
            var"##cse#1" = b
            var"##cse#2" = $(NaNMath.pow)(var"##cse#0", var"##cse#1")
        end
    )
    test_repr(
        Code.fast_toexpr(NaNMath.pow(a, b), ir, Dict()), quote
            var"##cse#0" = a
            var"##cse#1" = b
            var"##cse#2" = $(NaNMath.pow)(var"##cse#0", var"##cse#1")
        end
    )
    test_repr(
        Code.fast_toexpr(NaNMath.pow(a, b), ir, Dict{Any, Any}(:nanmath => true)), quote
            var"##cse#0" = a
            var"##cse#1" = b
            var"##cse#2" = $(NaNMath.pow)(var"##cse#0", var"##cse#1")
        end
    )

    test_repr(
        Code.fast_toexpr(a^2, ir, Dict()), quote
            var"##cse#0" = a
            var"##cse#1" = $(^)(var"##cse#0", 2)
        end
    )
    test_repr(
        Code.fast_toexpr(a^2, ir, Dict{Any, Any}(:nanmath => true)), quote
            var"##cse#0" = a
            var"##cse#1" = $(^)(var"##cse#0", 2)
        end
    )
    test_repr(
        Code.fast_toexpr(NaNMath.pow(a, 2), ir, Dict()), quote
            var"##cse#0" = a
            var"##cse#1" = $(^)(var"##cse#0", 2)
        end
    )
    test_repr(
        Code.fast_toexpr(NaNMath.pow(a, 2), ir, Dict{Any, Any}(:nanmath => true)), quote
            var"##cse#0" = a
            var"##cse#1" = $(^)(var"##cse#0", 2)
        end
    )

    test_repr(
        Code.fast_toexpr(a^-1, ir, Dict()),
        quote
            var"##cse#0" = 1
            var"##cse#1" = a
            var"##cse#2" = $(/)(var"##cse#0", var"##cse#1")
        end
    )
    test_repr(
        Code.fast_toexpr(a^-1, ir, Dict{Any, Any}(:nanmath => true)), quote
            var"##cse#0" = 1
            var"##cse#1" = a
            var"##cse#2" = $(/)(var"##cse#0", var"##cse#1")
        end
    )
    test_repr(
        Code.fast_toexpr(NaNMath.pow(a, -1), ir, Dict()), quote
            var"##cse#0" = 1
            var"##cse#1" = a
            var"##cse#2" = $(/)(var"##cse#0", var"##cse#1")
        end
    )
    test_repr(
        Code.fast_toexpr(NaNMath.pow(a, -1), ir, Dict{Any, Any}(:nanmath => true)),
        quote
            var"##cse#0" = 1
            var"##cse#1" = a
            var"##cse#2" = $(/)(var"##cse#0", var"##cse#1")
        end
    )

    test_repr(
        Code.fast_toexpr(a^-2, ir, Dict()),
        quote
            var"##cse#0" = 1
            var"##cse#1" = a
            var"##cse#2" = $(^)(var"##cse#1", 2)
            var"##cse#3" = $(/)(var"##cse#0", var"##cse#2")
        end
    )
    test_repr(
        Code.fast_toexpr(a^-2, ir, Dict{Any, Any}(:nanmath => true)),
        quote
            var"##cse#0" = 1
            var"##cse#1" = a
            var"##cse#2" = $(^)(var"##cse#1", 2)
            var"##cse#3" = $(/)(var"##cse#0", var"##cse#2")
        end
    )
    test_repr(
        Code.fast_toexpr(NaNMath.pow(a, -2), ir, Dict()),
        quote
            var"##cse#0" = 1
            var"##cse#1" = a
            var"##cse#2" = $(^)(var"##cse#1", 2)
            var"##cse#3" = $(/)(var"##cse#0", var"##cse#2")
        end
    )
    test_repr(
        Code.fast_toexpr(NaNMath.pow(a, -2), ir, Dict{Any, Any}(:nanmath => true)),
        quote
            var"##cse#0" = 1
            var"##cse#1" = a
            var"##cse#2" = $(^)(var"##cse#1", 2)
            var"##cse#3" = $(/)(var"##cse#0", var"##cse#2")
        end
    )

    @test eval(
        quote
            let a = 1, b = 2, arr = [1, 2]
                $(Code.fast_toexpr(Let([], MakeArray([a, b, a + b], :arr)), ir, Dict()))
            end
        end
    ) == [1, 2, 3]

    @test eval(
        Code.fast_toexpr(
            Let([a ← 1, b ← 2, :arr ← [1, 2]], MakeArray([a, b, a + b, a / b], :arr)), ir, Dict()
        )
    ) == [1, 2, 3, 1 / 2]

    test_repr(
        Code.fast_toexpr(
            Let(
                [DestructuredArgs([x(t), b, c], :foo) ← [3, 3, [1, 4]], DestructuredArgs([p, q], c)],
                x(t) + a + b + c
            ), ir, Dict{Any, Any}(:readable_variables => true)
        ),
        :(
            let __miscₛᵧₘ0 = Vector{Any}, __miscₛᵧₘ1 = 3, __miscₛᵧₘ2 = 3, __miscₛᵧₘ3 = Vector{Int64}, __miscₛᵧₘ4 = 1, __miscₛᵧₘ5 = 4, __miscₛᵧₘ6 = $(SymbolicUtils.Code.create_array)(__miscₛᵧₘ3, nothing, $(Val){1}(), $(Val){(2,)}(), __miscₛᵧₘ4, __miscₛᵧₘ5), __miscₛᵧₘ7 = $(SymbolicUtils.Code.create_array)(__miscₛᵧₘ0, nothing, $(Val){1}(), $(Val){(3,)}(), __miscₛᵧₘ1, __miscₛᵧₘ2, __miscₛᵧₘ6), foo = __miscₛᵧₘ7, __miscₛᵧₘ8 = foo[1], var"x(t)" = __miscₛᵧₘ8, __miscₛᵧₘ9 = foo[2], b = __miscₛᵧₘ9, __miscₛᵧₘ10 = foo[3], c = __miscₛᵧₘ10, __miscₛᵧₘ11 = c[1], p = __miscₛᵧₘ11, __miscₛᵧₘ12 = c[2], q = __miscₛᵧₘ12
                var"##cse#0" = a
                var"##cse#1" = b
                var"##cse#2" = c
                var"##cse#3" = var"x(t)"
                var"##cse#4" = $(+)(var"##cse#0", var"##cse#1", var"##cse#2", var"##cse#3")
            end
        )
    )

    test_repr(
        Code.fast_toexpr(Func([DestructuredArgs([a, b], c, inds = [:a, :b])], [], a + b), ir, Dict()),
        :(
            function ($c,)
                begin
                    __miscₛᵧₘ0 = c.a
                    a = __miscₛᵧₘ0
                    __miscₛᵧₘ1 = c.b
                    b = __miscₛᵧₘ1
                    var"##cse#0" = a
                    var"##cse#1" = b
                    var"##cse#2" = $(+)(var"##cse#0", var"##cse#1")
                end
            end
        )
    )

    @syms arr

    @test eval(
        Code.fast_toexpr(
            Let([a ← 1, b ← 2, arr ← [1, 2]], MakeArray([a, b, a + b, a / b], arr)), ir, Dict()
        )
    ) == [1, 2, 3, 1 / 2]

    @test eval(
        Code.fast_toexpr(
            Let([a ← 1, b ← 2, arr ← [1, 2]], MakeArray(view([a, b, a + b, a / b], :), arr)), ir, Dict()
        )
    ) == [1, 2, 3, 1 / 2]

    @test eval(
        Code.fast_toexpr(
            Let(
                [a ← 1, b ← 2, arr ← [1, 2]],
                MakeArray(PermutedDimsArray([a b; a + b a / b], (1, 2)), arr)
            ), ir, Dict()
        )
    ) == [1 2; 3 1 / 2]

    @test eval(
        Code.fast_toexpr(
            Let([a ← 1, b ← 2, arr ← [1, 2]], MakeArray(transpose([a b; a + b a / b]), arr)), ir, Dict()
        )
    ) == [1 3; 2 1 / 2]

    @test eval(
        Code.fast_toexpr(
            Let([a ← 1, b ← 2, arr ← [1, 2]], MakeArray(UpperTriangular([a b; a + b a / b]), arr)), ir, Dict()
        )
    ) == [1 2; 0 1 / 2]

    @test eval(
        Code.fast_toexpr(
            Let([a ← 1, b ← 2, arr ← [1, 2]], MakeArray([a b; a + b a / b], arr)), ir, Dict()
        )
    ) == [1 2; 3 1 / 2]

    @test eval(
        Code.fast_toexpr(
            Let([a ← 1, b ← 2, arr ← @SVector([1, 2])], MakeArray([a, b, a + b, a / b], arr)), ir, Dict()
        )
    ) === @SVector [1, 2, 3, 1 / 2]

    @test eval(
        Code.fast_toexpr(
            Let([a ← 1, b ← 2, arr ← @SVector([1, 2])], MakeArray([a b; a + b a / b], arr)), ir, Dict()
        )
    ) === @SMatrix [1 2; 3 1 / 2]

    @test eval(
        Code.fast_toexpr(
            Let(
                [a ← 1, b ← 2, arr ← @SLVector((:a, :b))(@SVector[1, 2])],
                MakeArray([a + b, a / b], arr)
            ), ir, Dict()
        )
    ) === @SLVector((:a, :b))(@SVector [3, 1 / 2])

    trackedarr = eval(
        Code.fast_toexpr(
            Let(
                [a ← ReverseDiff.track(1.0), b ← 2, arr ← ReverseDiff.track(ones(2))],
                MakeArray([a + b, a / b], arr)
            ), ir, Dict()
        )
    )
    @test trackedarr isa ReverseDiff.TrackedArray
    @test trackedarr == [3, 1 / 2]

    trackedarr = eval(
        Code.fast_toexpr(
            Let(
                [a ← ReverseDiff.track(1.0), b ← 2, arr ← ReverseDiff.track(ones(2))],
                MakeArray([a b; a + b a / b], arr)
            ), ir, Dict()
        )
    )
    @test trackedarr isa ReverseDiff.TrackedArray
    @test trackedarr == [1 2; 3 1 / 2]

    R1 = eval(
        Code.fast_toexpr(
            Let([a ← 1, b ← 2, arr ← @MVector([1, 2])], MakeArray([a, b, a + b, a / b], arr)), ir, Dict()
        )
    )
    @test R1 == (@MVector [1, 2, 3, 1 / 2]) && R1 isa MVector

    R2 = eval(
        Code.fast_toexpr(
            Let([a ← 1, b ← 2, arr ← @MVector([1, 2])], MakeArray([a b; a + b a / b], arr)), ir, Dict()
        )
    )
    @test R2 == (@MArray [1 2; 3 1 / 2]) && R2 isa MMatrix

    mksp = MakeSparseArray(
        sparse(
            [1, 2, 31, 32, 2],
            [1, 2, 31, 32, 2],
            [a, b, a + b, a / b, a - b + e]
        )
    )
    reference = sparse(
        [1, 2, 31, 32],
        [1, 2, 31, 32],
        [a, a + e, a + b, a / b]
    )

    test_repr(mksp.array, reference)

    test_repr(
        Code.fast_toexpr(Let([], mksp), ir, Dict()),
        :(
            let
                var"##cse#0" = (4,)
                var"##cse#1" = a
                var"##cse#2" = e
                var"##cse#3" = $(+)(var"##cse#1", var"##cse#2")
                var"##cse#4" = b
                var"##cse#5" = $(+)(var"##cse#1", var"##cse#4")
                var"##cse#6" = $(/)(var"##cse#1", var"##cse#4")
                var"##cse#7" = $(SymbolicUtils.array_literal)(var"##cse#0", var"##cse#1", var"##cse#3", var"##cse#5", var"##cse#6")
                __miscₛᵧₘ0 = $(sparse)([1, 2, 31, 32], [1, 2, 31, 32], var"##cse#7", 32, 32)
            end
        )
    )

    spvec = sparsevec([5], [a], 10)

    test_repr(
        Code.fast_toexpr(Let([], MakeSparseArray(spvec)), ir, Dict()),
        :(
            let
                var"##cse#0" = (1,)
                var"##cse#1" = a
                var"##cse#2" = $(SymbolicUtils.array_literal)(var"##cse#0", var"##cse#1")
                __miscₛᵧₘ0 = $(SparseVector)(10, [5], var"##cse#2")
            end
        )
    )

    test_repr(
        Code.fast_toexpr(Let([], MakeTuple((a, b, a + b))), ir, Dict()),
        :(
            let
                var"##cse#0" = a
                var"##cse#1" = b
                var"##cse#2" = $(+)(var"##cse#0", var"##cse#1")
                __miscₛᵧₘ0 = (var"##cse#0", var"##cse#1", var"##cse#2")
            end
        )
    )

    let
        @syms a b
        f = eval(Code.fast_toexpr(Func([a + b], [], a + b), ir, Dict()))
        @test @invokelatest(f(1)) == 1
        @test @invokelatest(f(2)) == 2

        f = eval(Code.fast_toexpr(Func([a, b], [], sqrt(a - b)), ir, Dict{Any, Any}(:nanmath => true)))
        @test isnan(@invokelatest f(0, 10))
        @test @invokelatest(f(10, 2)) ≈ sqrt(8)
    end

    let
        io = IOBuffer()
        twoπ = Base.Irrational{:twoπ}()
        for q in Base.Irrational[Base.MathConstants.catalan, Base.MathConstants.γ, π, Base.MathConstants.φ, ℯ, twoπ]
            Base.show(io, q)
            s1 = String(take!(io))
            SymbolicUtils.show_term(io, SymbolicUtils.Term{SymReal}(identity, [q]))
            s2 = String(take!(io))
            @test s1 == s2
        end
    end

    let
        @syms a b
        t = term(sum, [a, b, a + b, 3a + 2b, sqrt(b)]; type = Number)
        f = eval(Code.fast_toexpr(Func([a, b], [], t), ir, Dict()))
        @test @invokelatest(f(1.0, 2.0)) ≈ 13.0 + sqrt(2)
    end
end

@testset "Sparse array CSE" begin
    @syms x y z
    ir = IRStructure{SymReal}()
    arr = BS[x^2 + y^2 0 0; 0 sin(y^2 + z^2) 0; 0 0 z^2 + x^2]
    sarr = sparse(arr)
    fn = eval(Code.fast_toexpr(Func([x, y, z], [], sarr), ir, Dict()))

    expected = eval(toexpr(Let([x ← 1, y ← 2, z ← 3], sarr)))
    @test fn(1, 2, 3) ≈ expected
end

@testset "CSE does not alias constants with function arguments" begin
    # When build_function is given argument arrays containing constants (e.g., zeros
    # from erased cache variables), CSE should not replace identical constants in the
    # expression body with references to those argument positions. This is a regression
    # test for https://github.com/JuliaSymbolics/Symbolics.jl/issues/1811.
    @syms x1 x2 x3 x4 x5 x6
    x_vars = [x1, x2, x3, x4, x5, x6]
    ir = IRStructure{SymReal}()
    # A sparse diagonal jacobian-like expression
    ZERO = SymbolicUtils.Const{SymReal}(0)
    expr = fill(ZERO, 12, 6)
    for i in 1:6
        expr[i, i] = cos(x_vars[i])
        expr[i + 6, i] = -sin(x_vars[i])
    end
    # Second argument is all-zeros (simulating erased cache variables passed to build_function)
    zero_args = [SymbolicUtils.Const{SymReal}(0) for _ in 1:12]
    f_cse = eval(
        Code.fast_toexpr(
            Func(
                [
                    DestructuredArgs(x_vars, :arg1, inbounds = true, create_bindings = false),
                    DestructuredArgs(zero_args, :arg2, inbounds = true, create_bindings = false),
                ],
                [], MakeArray(expr, Array)
            ), ir, Dict()
        )
    )
    # Call with non-zero values for arg2 to expose incorrect aliasing
    result = @invokelatest f_cse(collect(1.0:6.0), ones(12) * 99.0)
    @test result[1, 2] == 0.0  # off-diagonal should be 0, NOT 99.0
    @test result[2, 1] == 0.0
    @test result[1, 1] ≈ cos(1.0)
    @test result[2, 2] ≈ cos(2.0)
end

@testset "`AtIndex` with symbolic index" begin
    @syms a b c::Matrix{Int}
    ir = IRStructure{SymReal}()
    ex = Let([], SetArray(false, c, [AtIndex(MakeArray([a, b], Array), [a + b, a - b])]))
    expr = quote
        let a = 1, b = 2, c = zeros(Int, 3, 3)
            $(Code.fast_toexpr(ex, ir, Dict()))
            c
        end
    end
    arr = eval(expr)
    @test arr[1] == 3
    @test arr[2] == -1
    for i in 3:length(arr)
        @test arr[i] == 0
    end
end

@testset "`ForLoop`" begin
    @syms a b c::Vector{Int}
    ir = IRStructure{SymReal}()
    ex = ForLoop(a, term(range, b^2, b^2 + 3), SetArray(false, c, [AtIndex(a, a + 1)]))
    expr = quote
        let b = 2, c = zeros(Int, 10)
            $(Code.fast_toexpr(ex, ir, Dict()))
            c
        end
    end
    arr = eval(expr)
    @test arr[4] == 5
    @test arr[5] == 6
    @test arr[6] == 7
    @test arr[7] == 8
    @test all(iszero, arr[1:3])
    @test all(iszero, arr[8:end])
end

@testset "`SetArray` with `return_arr`" begin
    @syms a b c::Vector{Int}
    ir = IRStructure{SymReal}()
    ex = Let([], SetArray(false, c, [3, 2, 1], false))
    expr = quote
        let b = 2, c = zeros(Int, 3)
            $(Code.fast_toexpr(ex, ir, Dict()))
        end
    end
    @test eval(expr) === nothing
    ex = Let([], SetArray(false, c, [3, 2, 1], true))
    expr = quote
        let b = 2, c = zeros(Int, 3)
            $(Code.fast_toexpr(ex, ir, Dict()))
        end
    end
    @test eval(expr) == [3, 2, 1]
end

@testset "`with_allocator`" begin
    @testset "`array_literal`" begin
        @syms x y z
        ir = IRStructure{SymReal}()
        arr = SymbolicUtils.Const{SymReal}([x, y + 2x^2 + sin(z), 2z + 1])
        wrapped = Code.with_allocator(ones, arr)
        test_repr(
            Code.fast_toexpr(wrapped, ir, Dict()),
            quote
                var"##cse#0" = ones
                var"##cse#1" = var"##cse#0"((3,))
                var"##cse#2" = x
                var"##cse#3" = z
                var"##cse#4" = $(sin)(var"##cse#3")
                var"##cse#5" = y
                var"##cse#6" = 2
                var"##cse#7" = $(^)(var"##cse#2", 2)
                var"##cse#8" = $(*)(var"##cse#6", var"##cse#7")
                var"##cse#9" = $(+)(var"##cse#4", var"##cse#5", var"##cse#8")
                var"##cse#10" = 1
                var"##cse#11" = $(*)(var"##cse#6", var"##cse#3")
                var"##cse#12" = $(+)(var"##cse#10", var"##cse#11")
                __miscₛᵧₘ0 = $(Code.fill_arr!)(var"##cse#1", $Val($((3,))), var"##cse#2", var"##cse#9", var"##cse#12")
            end
        )

        reference = eval(
            quote
                let x = 1, y = 2, z = 3
                    $(Code.fast_toexpr(arr, ir, Dict()))
                end
            end
        )
        value = eval(
            quote
                let x = 1, y = 2, z = 3
                    $(Code.fast_toexpr(wrapped, ir, Dict()))
                end
            end
        )
        @test isequal(reference, value)
    end

    @testset "`@arrayop`" begin
        @syms x[1:3] y[1:3]
        ir = IRStructure{SymReal}()
        arr = @arrayop (i,) x[i] * y[i]
        wrapped = Code.with_allocator(ones, arr)
        @test isequal(collect(arr), collect(wrapped))
        test_repr(
            Code.fast_toexpr(wrapped, ir, Dict()),
            quote
                var"##cse#0" = ones
                var"##cse#1" = var"##cse#0"((3,))
                _ = begin
                    for _1 in 1:1:3
                        begin
                            var"##cse#2" = x
                            var"##cse#3" = var"##cse#2"[_1]
                            var"##cse#4" = y
                            var"##cse#5" = var"##cse#4"[_1]
                            var"##cse#6" = $(*)(var"##cse#3", var"##cse#5")
                            __accum = $(+)(var"##cse#1"[$(CartesianIndex)(_1)], var"##cse#6")
                            _ = (var"##cse#1"[$(CartesianIndex)(_1)] = __accum)
                        end
                    end
                end
            end
        )
    end

    @testset "`Fill`" begin
        @syms x::Real
        ir = IRStructure{SymReal}()
        f1d = SymbolicUtils.Fill(SymbolicUtils.ShapeVecT((1:3,)))
        expr1d = f1d(x)

        xv = 2.0
        result1d = eval(quote
            let x = $xv
                $(Code.fast_toexpr(expr1d, ir, Dict()))
            end
        end)
        @test result1d == fill(xv, 3)

        wrapped1d = Code.with_allocator(ones, expr1d)
        result1d_wa = eval(quote
            let x = $xv
                $(Code.fast_toexpr(wrapped1d, ir, Dict()))
            end
        end)
        @test result1d_wa == fill(xv, 3)

        f2d = SymbolicUtils.Fill(SymbolicUtils.ShapeVecT((1:2, 1:4)))
        expr2d = f2d(x)
        result2d = eval(quote
            let x = $xv
                $(Code.fast_toexpr(expr2d, ir, Dict()))
            end
        end)
        @test result2d == fill(xv, 2, 4)

        wrapped2d = Code.with_allocator(ones, expr2d)
        result2d_wa = eval(quote
            let x = $xv
                $(Code.fast_toexpr(wrapped2d, ir, Dict()))
            end
        end)
        @test result2d_wa == fill(xv, 2, 4)
    end

    @testset "`Returns(buf)` allocator" begin
        @syms x y z buf[1:3]
        ir = IRStructure{SymReal}()
        arr = SymbolicUtils.Const{SymReal}([x, y, z])
        returns_alloc = SymbolicUtils.Term{SymReal}(Returns{SymReal}, (buf,))

        test_repr(
            Code.fast_toexpr(arr, ir, Dict{Any,Any}(Code.ALLOCATOR_REWRITES_KEY => returns_alloc)),
            quote
                var"##cse#0" = buf
                var"##cse#1" = var"##cse#0"
                var"##cse#2" = x
                var"##cse#3" = y
                var"##cse#4" = z
                __miscₛᵧₘ0 = $(Code.fill_arr!)(var"##cse#1", $Val($((3,))), var"##cse#2", var"##cse#3", var"##cse#4")
            end
        )

        reference = eval(quote
            let x = 1.0, y = 2.0, z = 3.0
                $(Code.fast_toexpr(arr, ir, Dict{Any,Any}()))
            end
        end)
        result = eval(quote
            let x = 1.0, y = 2.0, z = 3.0, buf = zeros(3)
                $(Code.fast_toexpr(arr, ir, Dict{Any,Any}(Code.ALLOCATOR_REWRITES_KEY => SymbolicUtils.Term{SymReal}(Returns{SymReal}, (buf,)))))
            end
        end)
        @test isequal(reference, result)
    end
end

@testset "fast_toexpr" begin
    @syms x[1:3] y[1:3] z[1:3]
    w = @makearray w[1:3, 1:3] begin
        w[1:1, 1:3] => x'
        w[2:2, 1:3] => @arrayop (1, i) y[i] + z[i]
        w[3:3, 1:1] => [1;;]
        w[3:3, 2:2] => [z[1];;]
        w[3:3, 3:3] => [z'z;;]
    end
    xv = rand(3)
    yv = rand(3)
    zv = rand(3)
    expected = eval(quote
        let x = $xv, y = $yv, z = $zv
            $(Code.toexpr(w))
        end
    end)
    actual = eval(quote
        let x = $xv, y = $yv, z = $zv
            $(Code.fast_toexpr(w, Dict{Any,Any}()))
        end
    end)
    @test expected ≈ actual
end

@testset "Fill in region" begin
    @syms a::Real b::Real
    f = SymbolicUtils.Fill(SymbolicUtils.ShapeVecT((1:3,)))
    w = @makearray w[1:6] begin
        w[1:3] => f(a)
        w[4:6] => f(b)
    end
    av = 2.0
    bv = 5.0
    wv = eval(quote
        let a = $av, b = $bv
            $(Code.fast_toexpr(w, Dict{Any,Any}()))
        end
    end)
    @test wv[1:3] == fill(av, 3)
    @test wv[4:6] == fill(bv, 3)
end

# Helper: build a CodegenState, run codegen for `expr`, and append the result symbol so the
# block evaluates to the generated buffer (needed for ArrayOp / Fill whose codegen writes
# into a buffer rather than returning it as the last block statement).
function _codegen_to_block(ir, expr, rewrites = Dict{Any,Any}())
    block = Expr(:block)
    cs = Code.CodegenState(block, block, ir, rewrites)
    result_sym = cs(expr)
    push!(block.args, result_sym)
    return block
end

@testset "codegen on non-canonical `IRStructure`" begin
    # Extract the `term` field from an ArrayOp (used by Fill / map / mapreduce).
    # That inner Term must be pre-populated before replace_node! so that its
    # outneighbors in the graph already point to the replaced node.
    function _arrayop_term(expr)
        @match expr begin
            BSImpl.ArrayOp(; term) => term
            _ => error("expected ArrayOp")
        end
    end

    @testset "generic op" begin
        # sin(a + b) with a+b → a*b: codegen should produce sin(a*b)
        @syms a::Real b::Real
        ir = IRStructure{SymReal}()
        populate_ir!(ir, sin(a + b))
        replace_node!(ir, a + b, a * b)
        @test !isempty(ir.non_canonical_idxs)
        expr = Code.fast_toexpr(sin(a + b), ir, Dict{Any,Any}(:sort_addmul => false))
        result = eval(quote let a = 2.0, b = 3.0; $expr end end)
        @test result ≈ sin(2.0 * 3.0)
    end

    @testset "nanmath op" begin
        @syms a::Real b::Real
        ir = IRStructure{SymReal}()
        populate_ir!(ir, sin(a + b))
        replace_node!(ir, a + b, a * b)
        @test !isempty(ir.non_canonical_idxs)
        expr = Code.fast_toexpr(
            sin(a + b), ir, Dict{Any,Any}(:nanmath => true, :sort_addmul => false)
        )
        result = eval(quote let a = 2.0, b = 3.0; $expr end end)
        @test result ≈ sin(2.0 * 3.0)
    end

    @testset "`+` and `*`" begin
        @syms a::Real b::Real c::Real d::Real
        let ir = IRStructure{SymReal}()
            populate_ir!(ir, a + b + c)
            replace_node!(ir, a, d)
            @test !isempty(ir.non_canonical_idxs)
            expr = Code.fast_toexpr(a + b + c, ir, Dict{Any,Any}(:sort_addmul => false))
            result = eval(quote let a = 1.0, b = 2.0, c = 3.0, d = 10.0; $expr end end)
            @test result ≈ 10.0 + 2.0 + 3.0
        end

        let ir = IRStructure{SymReal}()
            populate_ir!(ir, a * b * c)
            replace_node!(ir, a, d)
            @test !isempty(ir.non_canonical_idxs)
            expr = Code.fast_toexpr(a * b * c, ir, Dict{Any,Any}(:sort_addmul => false))
            result = eval(quote let a = 1.0, b = 2.0, c = 3.0, d = 10.0; $expr end end)
            @test result ≈ 10.0 * 2.0 * 3.0
        end
    end

    @testset "`^`" begin
        @syms a::Real b::Real c::Real
        # symbolic exponent: a^b with a → c
        let ir = IRStructure{SymReal}()
            populate_ir!(ir, a^b)
            replace_node!(ir, a, c)
            @test !isempty(ir.non_canonical_idxs)
            expr = Code.fast_toexpr(a^b, ir, Dict{Any,Any}(:sort_addmul => false))
            result = eval(quote let a = 2.0, b = 3.0, c = 4.0; $expr end end)
            @test result ≈ 4.0^3.0
        end
        # constant exponent: a^2 with a → c
        let ir = IRStructure{SymReal}()
            populate_ir!(ir, a^2)
            replace_node!(ir, a, c)
            @test !isempty(ir.non_canonical_idxs)
            expr = Code.fast_toexpr(a^2, ir, Dict{Any,Any}(:sort_addmul => false))
            result = eval(quote let a = 2.0, c = 3.0; $expr end end)
            @test result ≈ 3.0^2
        end
    end

    @testset "`ifelse`" begin
        @syms a::Real b::Real c::Real d::Real
        cond = a < 0
        ir = IRStructure{SymReal}()
        populate_ir!(ir, ifelse(cond, b, c))
        replace_node!(ir, b, d)
        @test !isempty(ir.non_canonical_idxs)
        expr = Code.fast_toexpr(ifelse(cond, b, c), ir, Dict{Any,Any}(:sort_addmul => false))
        result = eval(quote let a = -1.0, b = 10.0, c = 20.0, d = 30.0; $expr end end)
        @test result ≈ 30.0  # a < 0 is true, so uses d (replaced from b)
    end

    @testset "`getindex`" begin
        @syms x[1:3]::Real idx1::Int idx2::Int
        ir = IRStructure{SymReal}()
        populate_ir!(ir, x[idx1])
        replace_node!(ir, idx1, idx2)
        @test !isempty(ir.non_canonical_idxs)
        expr = Code.fast_toexpr(x[idx1], ir, Dict{Any,Any}())
        result = eval(quote let x = [10, 20, 30], idx1 = 1, idx2 = 2; $expr end end)
        @test result == 20  # x[idx2] = x[2] = 20
    end

    @testset "`ArrayOp`" begin
        @syms xv[1:3]::Real yv[1:3]::Real zv[1:3]::Real
        arr = @arrayop (i,) xv[i] * yv[i]
        ir = IRStructure{SymReal}()
        populate_ir!(ir, arr)
        replace_node!(ir, Const{SymReal}(yv), Const{SymReal}(zv))
        @test !isempty(ir.non_canonical_idxs)
        block = _codegen_to_block(ir, arr, Dict{Any,Any}(:sort_addmul => false))
        xdata = [1.0, 2.0, 3.0]; ydata = [10.0, 10.0, 10.0]; zdata = [4.0, 5.0, 6.0]
        result = eval(quote let xv = $xdata, yv = $ydata, zv = $zdata; $block end end)
        @test result ≈ xdata .* zdata
    end

    @testset "`Fill`" begin
        @syms a::Real b::Real
        f = SymbolicUtils.Fill(SymbolicUtils.ShapeVecT((1:3,)))
        fill_expr = f(a)
        ir = IRStructure{SymReal}()
        populate_ir!(ir, fill_expr)
        # Pre-populate the inner Term so its graph edges already exist before replace_node!
        populate_ir!(ir, _arrayop_term(fill_expr))
        replace_node!(ir, a, b)
        @test !isempty(ir.non_canonical_idxs)
        block = _codegen_to_block(ir, fill_expr)
        result = eval(quote let a = 2.0, b = 5.0; $block end end)
        @test result == fill(5.0, 3)
    end

    @testset "`ArrayMaker`" begin
        @syms a::Real b::Real c::Real
        f = SymbolicUtils.Fill(SymbolicUtils.ShapeVecT((1:3,)))
        w = @makearray w[1:6] begin
            w[1:3] => f(a)
            w[4:6] => f(b)
        end
        ir = IRStructure{SymReal}()
        populate_ir!(ir, w)
        replace_node!(ir, a, c)
        @test !isempty(ir.non_canonical_idxs)
        expr = Code.fast_toexpr(w, ir, Dict{Any,Any}(:sort_addmul => false))
        av = 2.0; bv = 5.0; cv = 7.0
        result = eval(quote let a = $av, b = $bv, c = $cv; $expr end end)
        @test result[1:3] == fill(cv, 3)
        @test result[4:6] == fill(bv, 3)
    end

    @testset "`array_literal`" begin
        @syms a::Real b::Real c::Real d::Real
        # without allocator
        arr_lit = Const{SymReal}([a, b, c])
        let ir = IRStructure{SymReal}()
            populate_ir!(ir, arr_lit)
            replace_node!(ir, a, d)
            @test !isempty(ir.non_canonical_idxs)
            expr = Code.fast_toexpr(arr_lit, ir, Dict{Any,Any}())
            result = eval(quote let a = 1.0, b = 2.0, c = 3.0, d = 10.0; $expr end end)
            @test result ≈ [10.0, 2.0, 3.0]
        end
        # with allocator
        let ir = IRStructure{SymReal}()
            populate_ir!(ir, arr_lit)
            replace_node!(ir, a, d)
            @test !isempty(ir.non_canonical_idxs)
            wrapped = Code.with_allocator(ones, arr_lit)
            expr = Code.fast_toexpr(wrapped, ir, Dict{Any,Any}(:sort_addmul => false))
            result = eval(quote let a = 1.0, b = 2.0, c = 3.0, d = 10.0; $expr end end)
            @test result ≈ [10.0, 2.0, 3.0]
        end
    end

    @testset "`Mapper`" begin
        @syms av[1:3]::Real bv[1:3]::Real cv[1:3]::Real
        ex_map = map(+, av, bv)
        ir = IRStructure{SymReal}()
        populate_ir!(ir, ex_map)
        populate_ir!(ir, _arrayop_term(ex_map))
        replace_node!(ir, Const{SymReal}(bv), Const{SymReal}(cv))
        @test !isempty(ir.non_canonical_idxs)
        block = _codegen_to_block(ir, ex_map, Dict{Any,Any}(:sort_addmul => false))
        xdata = [1.0, 2.0, 3.0]; ydata = [10.0, 10.0, 10.0]; zdata = [4.0, 5.0, 6.0]
        result = eval(quote let av = $xdata, bv = $ydata, cv = $zdata; $block end end)
        @test result ≈ xdata .+ zdata
    end

    @testset "`Mapreducer`" begin
        @syms av[1:3]::Real bv[1:3]::Real cv[1:3]::Real
        ex_mapred = mapreduce(+, +, av, bv)
        ir = IRStructure{SymReal}()
        populate_ir!(ir, ex_mapred)
        populate_ir!(ir, _arrayop_term(ex_mapred))
        replace_node!(ir, Const{SymReal}(bv), Const{SymReal}(cv))
        @test !isempty(ir.non_canonical_idxs)
        block = _codegen_to_block(ir, ex_mapred, Dict{Any,Any}(:sort_addmul => false))
        xdata = [1.0, 2.0, 3.0]; ydata = [10.0, 10.0, 10.0]; zdata = [4.0, 5.0, 6.0]
        result = eval(quote let av = $xdata, bv = $ydata, cv = $zdata; $block end end)
        @test result ≈ sum(xdata .+ zdata)
    end
end

@testset "batched_setindex!" begin
    # NTuple of values, NTuple of CartesianIndex (1D)
    buf = zeros(Int, 5)
    Code.batched_setindex!(buf, (10, 20, 30), (CartesianIndex(1), CartesianIndex(3), CartesianIndex(5)))
    @test buf == [10, 0, 20, 0, 30]

    # NTuple of values, NTuple of CartesianIndex (2D)
    buf2d = zeros(Int, 3, 3)
    Code.batched_setindex!(buf2d, (7, 8), (CartesianIndex(1, 2), CartesianIndex(3, 2)))
    @test buf2d[1, 2] == 7
    @test buf2d[3, 2] == 8
    @test count(!iszero, buf2d) == 2

    # Broadcast single value, array of CartesianIndex (1D)
    buf = zeros(Int, 5)
    Code.batched_setindex!(buf, 42, [CartesianIndex(1), CartesianIndex(3), CartesianIndex(5)])
    @test buf == [42, 0, 42, 0, 42]

    # Broadcast single value, array of CartesianIndex (2D)
    buf2d = zeros(Int, 3, 3)
    Code.batched_setindex!(buf2d, -1, [CartesianIndex(1, 1), CartesianIndex(2, 2), CartesianIndex(3, 3)])
    @test buf2d == [-1 0 0; 0 -1 0; 0 0 -1]

    # Empty index array is a no-op
    buf = zeros(Int, 3)
    Code.batched_setindex!(buf, 99, CartesianIndex{1}[])
    @test buf == [0, 0, 0]
end

@testset "ArrayMaker batched scalar-write codegen" begin
    @syms a::Real b::Real

    # 20-element array: exercises the batched_setindex! codegen path.
    # FILL_ARR_LIMIT == 16, so arrays of size > 16 use batched_setindex! for scalar writes.
    # Entries 1–3 are 1 (→ idxs_buffer broadcast path for value 1).
    # Entries 4–5 are -1 (→ idxs_buffer broadcast path for value -1).
    # Entries 6–20 are symbolic (→ NTuple batching, split across multiple calls because
    # BATCHED_SETINDEX_BATCH_SIZE == 8).
    w = @makearray w[1:20] begin
        w[1:1]   => [1]
        w[2:2]   => [1]
        w[3:3]   => [1]
        w[4:4]   => [-1]
        w[5:5]   => [-1]
        w[6:6]   => [a]
        w[7:7]   => [b]
        w[8:8]   => [a + b]
        w[9:9]   => [2a]
        w[10:10] => [2b]
        w[11:11] => [a - b]
        w[12:12] => [3a]
        w[13:13] => [a^2]
        w[14:14] => [b^2]
        w[15:15] => [a + 1]
        w[16:16] => [b + 1]
        w[17:17] => [a * b]
        w[18:18] => [a - 1]
        w[19:19] => [b - 1]
        w[20:20] => Const{SymReal}([a + b + 1])
    end
    av = 3.0
    bv = 2.0
    result = eval(quote
        let a = $av, b = $bv
            $(Code.fast_toexpr(w, Dict{Any,Any}()))
        end
    end)
    expected = [1.0, 1.0, 1.0, -1.0, -1.0, av, bv, av+bv, 2av, 2bv, av-bv, 3av, av^2, bv^2, av+1, bv+1, av*bv, av-1, bv-1, av+bv+1]
    @test result ≈ expected

    @testset "later scalar writes overwrite earlier ones" begin
        # Scalar writes to the same index are stored in a Dict; later entries win.
        w2 = @makearray w2[1:20] begin
            w2[1:1]  => [a]
            w2[2:2]  => [1]
            w2[3:3]  => [1]
            w2[4:4]  => [1]
            w2[5:5]  => [1]
            w2[6:6]  => [1]
            w2[7:7]  => [1]
            w2[8:8]  => [1]
            w2[9:9]  => [1]
            w2[10:10] => [1]
            w2[11:11] => [1]
            w2[12:12] => [1]
            w2[13:13] => [1]
            w2[14:14] => [1]
            w2[15:15] => [1]
            w2[16:16] => [1]
            w2[17:17] => [1]
            w2[18:18] => [1]
            w2[19:19] => [1]
            w2[20:20] => [1]
            w2[1:1]  => Const{SymReal}([b])
        end
        result2 = eval(quote
            let a = $av, b = $bv
                $(Code.fast_toexpr(w2, Dict{Any,Any}()))
            end
        end)
        @test result2[1] ≈ bv
        @test all(result2[2:end] .≈ 1.0)
    end

    @testset "scalar writes flushed before block write" begin
        @syms xv[1:3]::Real
        # Scalar writes at indices 1–17 followed by a block write at 18–20.
        # The block write must trigger flushing of all preceding scalar writes.
        w3 = @makearray w3[1:20] begin
            w3[1:1]   => [1]
            w3[2:2]   => [1]
            w3[3:3]   => [1]
            w3[4:4]   => [1]
            w3[5:5]   => [1]
            w3[6:6]   => [1]
            w3[7:7]   => [1]
            w3[8:8]   => [1]
            w3[9:9]   => [1]
            w3[10:10] => [1]
            w3[11:11] => [1]
            w3[12:12] => [1]
            w3[13:13] => [1]
            w3[14:14] => [1]
            w3[15:15] => [1]
            w3[16:16] => [1]
            w3[17:17] => [1]
            w3[18:20] => xv
        end
        xdata = [10.0, 20.0, 30.0]
        result3 = eval(quote
            let xv = $xdata
                $(Code.fast_toexpr(w3, Dict{Any,Any}()))
            end
        end)
        @test all(result3[1:17] .≈ 1.0)
        @test result3[18:20] ≈ xdata
    end
end

@testset "`replace_node!` on an argument of `ArrayOp` with a `term` codegens correctly" begin
    @syms x[1:3]
    ir = IRStructure{SymReal}()
    inner = x .+ 1
    inner_idx = populate_ir!(ir, inner)
    outer_idx = populate_ir!(ir, sum(inner))
    replace_node!(ir, ir[inner_idx], x .+ 2)
    x_val = [1, 2, 3]
    reference = sum(x_val .+ 2)
    value = eval(quote
        let x = $x_val
            $(Code.fast_toexpr(ir[outer_idx], ir, Dict()))
        end
    end)
    @test reference == value
end

@testset "`LHS_HOOK_KEY`" begin
    @syms x
    ir = IRStructure{SymReal}()
    rw = Dict()
    rw[Code.LHS_HOOK_KEY] = (_, _, lhs) -> :($lhs::Any)
    expr = Code.fast_toexpr(sin(x), ir, rw)
    test_repr(expr, quote
        var"##cse#0"::Any = x
        var"##cse#1"::Any = $sin(var"##cse#0")
    end)
end

@testset "Matrix multiplication CSEs common prefixes" begin
    @syms x[1:3, 1:3] y[1:3, 1:3] z[1:3, 1:3] w[1:3, 1:3]
    ir = IRStructure{SymReal}()
    rw = Dict()
    expr = Code.fast_toexpr((x * y * z) \ (x * y * w), ir, rw)
    test_repr(expr, quote
        var"##cse#0" = x
        var"##cse#1" = y
        var"##cse#2" = $(*)(var"##cse#0", var"##cse#1")
        var"##cse#3" = z
        var"##cse#4" = $(*)(var"##cse#2", var"##cse#3")
        var"##cse#5" = w
        var"##cse#6" = $(*)(var"##cse#2", var"##cse#5")
        var"##cse#7" = $(\)(var"##cse#4", var"##cse#6")
    end)
end
