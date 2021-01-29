using Test, SymbolicUtils
using SymbolicUtils.Code
using SymbolicUtils.Code: LazyState
using StaticArrays
using LabelledArrays

test_repr(a, b) = @test repr(Base.remove_linenums!(a)) == repr(Base.remove_linenums!(b))

#@testset "toexpr level 1" begin
    @syms a b c d e t x(t) y(t) z(t)
    @test toexpr(Assignment(a, b)) == :(a = b)
    @test toexpr(a ← b) == :(a = b)
    @test toexpr(a+b) == :($(+)(a, b))
    @test toexpr(a+b) == :($(+)(a, b))
    @test toexpr(a^b) == :($(^)(a, b))
    @test toexpr(a^2) == :($(^)(a, 2))
    @test toexpr(a^-2) == :($(^)($(inv)(a), 2))
    @test toexpr(x(t)+y(t)) == :($(+)(x(t), y(t)))
    @test toexpr(x(t)+y(t)+x(t+1)) == :($(+)(x(t), y(t), x($(+)(1, t))))
    s = LazyState()
    push!(s.symbolify, x(t))
    push!(s.symbolify, y(t))
    @test toexpr(x(t)+y(t)+x(t+1), s) == :($(+)(var"x(t)", var"y(t)", x($(+)(1, t))))

    ex = :(let a = 3, b = $(+)(1,a)
               $(+)(a, b)
           end)

    test_repr(toexpr(Let([a ← 3, b ← 1+a], a + b)), ex)

    test_repr(toexpr(Func([],[], a+b)) |>Base.remove_linenums!, :(function ()
            $(+)(a, b)
        end))

    test_repr(toexpr(Func([x(t), x],[b ← a+2, y(t) ← b], x(t)+x(t+1)+b+y(t))),
              :(function (var"x(t)", x; b = $(+)(2, a), var"y(t)" = b)
                    $(+)(b, var"x(t)", var"y(t)", x($(+)(1, t)))
                end))
    test_repr(toexpr(Func([DestructuredArgs([x, x(t)], :state),
                           DestructuredArgs((a, b), :params)], [],
                          x(t+1) + x(t) + a  + b)),
              :(function (state, params)
                    let x = state[1], var"x(t)" = state[2], a = params[1], b = params[2]
                        $(+)(a, b, var"x(t)", x($(+)(1, t)))
                    end
                end))
    test_repr(toexpr(SetArray(false, a, [x(t), AtIndex(9, b), c])),
              quote
                  a[1] = x(t)
                  a[9] = b
                  a[3] = c
                  nothing
              end)
    @test toexpr(SetArray(true, a, [x(t), AtIndex(9, b), c])).head == :macrocall

    test_repr(toexpr(LiteralExpr(:(let x=1, y=2
                                       $(sin(a+b))
                                   end))),
              :(let x = 1, y = 2
                    $(sin)($(+)(a, b))
                end))

    test_repr(toexpr(MakeArray([a,b,a+b], :arr)),
              quote
                  $(SymbolicUtils.Code.create_array)(typeof(arr), nothing, Val{(3,)}(), a, b, $(+)(a, b))
              end)

    toexpr(Let([a ← 1, b ← 2, :arr ← [1,2]],
               MakeArray([a,b,a+b,a/b], :arr)))

    @syms arr

    @test eval(toexpr(Let([a ← 1, b ← 2, arr ← [1,2]],
                          MakeArray([a,b,a+b,a/b], arr)))) == [1, 2, 3, 1/2]

    @test eval(toexpr(Let([a ← 1, b ← 2, arr ← [1,2]],
                          MakeArray([a b;a+b a/b], arr)))) == [1 2; 3 1/2]

    @test eval(toexpr(Let([a ← 1, b ← 2, arr ← @SVector([1,2])],
                          MakeArray([a,b,a+b,a/b], arr)))) === @SVector [1, 2, 3, 1/2]

    @test eval(toexpr(Let([a ← 1, b ← 2, arr ← @SVector([1,2])],
                          MakeArray([a b;a+b a/b], arr)))) === @SMatrix [1 2; 3 1/2]

    @test eval(toexpr(Let([a ← 1, b ← 2, arr ← @SLVector((:a, :b))(@SVector[1,2])],
                          MakeArray([a+b,a/b], arr)))) === @SLVector((:a, :b))(@SVector [3, 1/2])
#end
#
