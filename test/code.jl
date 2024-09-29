using Test, SymbolicUtils
using NaNMath
using SymbolicUtils.Code
using SymbolicUtils.Code: LazyState
using StaticArrays
using LabelledArrays
using SparseArrays
using ReverseDiff
using LinearAlgebra

test_repr(a, b) = @test repr(Base.remove_linenums!(a)) == repr(Base.remove_linenums!(b))
nanmath_st = Code.NameState()
nanmath_st.rewrites[:nanmath] = true

@testset "Code" begin
    @syms a b c d e p q t x(t) y(t) z(t)
    @test toexpr(Assignment(a, b)) == :(a = b)
    @test toexpr(a ← b) == :(a = b)
    @test toexpr(a+b) == :($(+)(a, b))
    @test toexpr(a*b*c*d*e) == :($(*)($(*)($(*)($(*)(a, b), c), d), e))
    @test toexpr(a+b+c+d+e) == :($(+)($(+)($(+)($(+)(a, b), c), d), e))
    @test toexpr(a+b) == :($(+)(a, b))
    @test toexpr(a^b) == :($(^)(a, b))
    @test toexpr(a^2) == :($(^)(a, 2))
    @test toexpr(a^-2) == :($(/)(1, $(^)(a, 2)))
    @test toexpr(x(t)+y(t)) == :($(+)(x(t), y(t)))
    @test toexpr(x(t)+y(t)+x(t+1)) == :($(+)($(+)(x(t), y(t)), x($(+)(1, t))))
    s = LazyState()
    Code.union_rewrites!(s.rewrites, [x(t), y(t)])
    @test toexpr(x(t)+y(t)+x(t+1), s) == :($(+)($(+)(var"x(t)", var"y(t)"), x($(+)(1, t))))

    ex = :(let a = 3, b = $(+)(1,a)
               $(+)(a, b)
           end)

    test_repr(toexpr(Let([a ← 3, b ← 1+a], a + b)), ex)

    test_repr(toexpr(Func([],[], a+b)) |>Base.remove_linenums!, :(function ()
            $(+)(a, b)
        end))

    test_repr(toexpr(Func([x(t), x],[b ← a+2, y(t) ← b], x(t)+x(t+1)+b+y(t))),
              :(function (var"x(t)", x; b = $(+)(2, a), var"y(t)" = b)
                    $(+)($(+)($(+)(b, var"x(t)"), var"y(t)"), x($(+)(1, t)))
                end))
    test_repr(toexpr(Func([DestructuredArgs([x, x(t)], :state),
                           DestructuredArgs((a, b), :params)], [],
                          x(t+1) + x(t) + a  + b)),
              :(function (state, params)
                    begin
                        x = state[1]
                        var"x(t)" = state[2]
                        a = params[1]
                        b = params[2]
                        $(+)($(+)($(+)(a, b), var"x(t)"), x($(+)(1, t)))
                    end
                end))

    test_repr(toexpr(Func([DestructuredArgs([x, x(t)], :state, create_bindings=false),
                           DestructuredArgs((a, b), :params, create_bindings=false)], [],
                          x(t+1) + x(t) + a  + b)),
              :(function (state, params)
                    begin
                        $(+)($(+)($(+)(params[1], params[2]), state[2]), state[1]($(+)(1, t)))
                    end
                end))


    test_repr(toexpr(Func([],[],:(rand()), [Expr(:meta, :inline)])),
              :(function ()
                    $(Expr(:meta, :inline))
                    rand()
                end))

    ex = toexpr(Func([DestructuredArgs([x, x(t)], :state, inbounds=true)], [], x(t+1) + x(t)))
    ex = Base.remove_linenums!(ex)
    for e ∈ ex.args[2].args[1].args[1:2]
        @test e.args[2].head == :macrocall
    end

    test_repr(toexpr(SetArray(false, a, [x(t), AtIndex(9, b), c])),
              quote
                  a[1] = x(t)
                  a[9] = b
                  a[3] = c
                  nothing
              end)
    @test toexpr(SetArray(true, a, [x(t), AtIndex(9, b), c])).head == :macrocall


    @test toexpr(NaNMath.pow(a, b)) == :($(NaNMath.pow)(a, b))

    f = GlobalRef(NaNMath, :sin)
    test_repr(toexpr(LiteralExpr(:(let x=1, y=2
                                       $(sin(a+b))
                                   end)), nanmath_st),
              :(let x = 1, y = 2
                    $(f)($(+)(a, b))
                end))
    test_repr(toexpr(LiteralExpr(:(let x=1, y=2
                                       $(sin(a+b))
                                   end))),
              :(let x = 1, y = 2
                    $(sin)($(+)(a, b))
                end))

    test_repr(toexpr(MakeArray([a,b,a+b], :arr)),
              quote
                  $(SymbolicUtils.Code.create_array)(typeof(arr), nothing, Val{1}(), Val{(3,)}(), a, b, $(+)(a, b))
              end)

    toexpr(Let([a ← 1, b ← 2, :arr ← [1,2]],
               MakeArray([a,b,a+b,a/b], :arr)))

    test_repr(toexpr(Let([DestructuredArgs([x(t),b,c], :foo) ← [3,3,[1,4]],
                          DestructuredArgs([p,q], c)],
                         x(t)+a+b+c)),
              :(let foo = Any[3, 3, [1, 4]],
                    var"x(t)" = foo[1], b = foo[2], c = foo[3],
                    p = c[1], q = c[2]
                    $(+)($(+)($(+)(a, b), c), var"x(t)")
                end))

    test_repr(toexpr(Func([DestructuredArgs([a,b],c,inds=[:a, :b])], [],
                          a + b)),
              :(function (c,)
                    begin
                        a = c.a
                        b = c.b
                        $(+)(a, b)
                    end
                end))
    @syms arr

    @test eval(toexpr(Let([a ← 1, b ← 2, arr ← [1,2]],
                          MakeArray([a,b,a+b,a/b], arr)))) == [1, 2, 3, 1/2]

    @test eval(toexpr(Let([a ← 1, b ← 2, arr ← [1,2]],
                          MakeArray(view([a,b,a+b,a/b], :), arr)))) == [1, 2, 3, 1/2]

    @test eval(toexpr(Let([a ← 1, b ← 2, arr ← [1,2]],
                          MakeArray(PermutedDimsArray([a b;a+b a/b], (1,2)), arr)))) == [1 2 ; 3  1/2]

    @test eval(toexpr(Let([a ← 1, b ← 2, arr ← [1,2]],
                          MakeArray(transpose([a b;a+b a/b]), arr)))) == [1 3;2 1/2]

    @test eval(toexpr(Let([a ← 1, b ← 2, arr ← [1,2]],
                          MakeArray(UpperTriangular([a b;a+b a/b]), arr)))) == [1 2;0 1/2]

    @test eval(toexpr(Let([a ← 1, b ← 2, arr ← [1,2]],
                          MakeArray([a b;a+b a/b], arr)))) == [1 2; 3 1/2]

    @test eval(toexpr(Let([a ← 1, b ← 2, arr ← @SVector([1,2])],
                          MakeArray([a,b,a+b,a/b], arr)))) === @SVector [1, 2, 3, 1/2]

    @test eval(toexpr(Let([a ← 1, b ← 2, arr ← @SVector([1,2])],
                          MakeArray([a b;a+b a/b], arr)))) === @SMatrix [1 2; 3 1/2]

    @test eval(toexpr(Let([a ← 1, b ← 2, arr ← @SLVector((:a, :b))(@SVector[1,2])],
                          MakeArray([a+b,a/b], arr)))) === @SLVector((:a, :b))(@SVector [3, 1/2])

    trackedarr = eval(toexpr(Let([a ← ReverseDiff.track(1.0), b ← 2, arr ← ReverseDiff.track(ones(2))],
                          MakeArray([a+b,a/b], arr))))
    @test trackedarr isa ReverseDiff.TrackedArray
    @test trackedarr == [3, 1/2]

    trackedarr = eval(toexpr(Let([a ← ReverseDiff.track(1.0), b ← 2, arr ← ReverseDiff.track(ones(2))],
                          MakeArray([a b; a+b a/b], arr))))
    @test trackedarr isa ReverseDiff.TrackedArray
    @test trackedarr == [1 2; 3 1/2]
    

    R1 = eval(toexpr(Let([a ← 1, b ← 2, arr ← @MVector([1,2])],MakeArray([a,b,a+b,a/b], arr))))
    @test R1 == (@MVector [1, 2, 3, 1/2]) && R1 isa MVector

    R2 = eval(toexpr(Let([a ← 1, b ← 2, arr ← @MVector([1,2])],MakeArray([a b;a+b a/b], arr))))
    @test R2 == (@MArray [1 2; 3 1/2]) && R2 isa MMatrix

    mksp = MakeSparseArray(sparse([1,2,31,32,2],
                                  [1,2,31,32,2],
                                  [a, b, a+b, a/b, a-b+e]))
    reference = sparse([1,2,31,32],
                     [1,2,31,32],
                     [a, a+e, a+b, a/b])

    test_repr(mksp.array, reference)

    test_repr(toexpr(mksp),
              :(SparseMatrixCSC(32, 32,
                                $(reference.colptr),
                                $(reference.rowval),
                                [$(map(toexpr, reference.nzval)...)])))


    spvec = sparsevec([5], [a], 10)

    test_repr(toexpr(MakeSparseArray(spvec)),
              :(SparseVector(10, $(spvec.nzind), [a])))
    test_repr(toexpr(MakeTuple((a, b, a+b))),
              :((a,b,$(+)(a,b))))

    @test SpawnFetch{Multithreaded}([()->1,()->2],vcat)|>toexpr|>eval == [1,2]
    @test @elapsed(SpawnFetch{Multithreaded}([:(()->sleep(2)),
                                              Func([:x],
                                                   [],
                                                   :(sleep(x)))],
                                             [(),
                                              (2,)],
                                             vcat)|>toexpr|>eval) < 3

    let
        @syms a b

        f = eval(toexpr(Func([a+b], [], a+b)))
        @test f(1) == 1
        @test f(2) == 2

        f = eval(toexpr(Func([a, b], [], sqrt(a - b)), nanmath_st))
        @test isnan(f(0, 10))
        @test f(10, 2) ≈ sqrt(8)
    end

    let
        io = IOBuffer()
        twoπ = Base.Irrational{:twoπ}()
        for q ∈ Base.Irrational[Base.MathConstants.catalan, Base.MathConstants.γ, π, Base.MathConstants.φ, ℯ, twoπ]
            Base.show(io, q)
            s1 = String(take!(io))
            SymbolicUtils.show_term(io, SymbolicUtils._Term(identity, [q]))
            s2 = String(take!(io))
            @test s1 == s2
        end
    end

    let
        @syms a b

        t = term(sum, [a, b, a + b, 3a + 2b, sqrt(b)]; type = Number)
        f = eval(toexpr(Func([a, b], [], t)))
        @test f(1.0, 2.0) ≈ 13.0 + sqrt(2)
    end
end
