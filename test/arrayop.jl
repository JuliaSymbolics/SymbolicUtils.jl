using SymbolicUtils
using SymbolicUtils: BasicSymbolic, Term, Const, ArgsT, ShapeVecT, scalarize, symtype, isarrayop
using SymbolicUtils.Code
using LinearAlgebra
using Test

limit2(a, N) = a == N + 1 ? 1 : a == 0 ? N : a
limit2(a::BasicSymbolic{T}, N) where {T} = Term{T}(limit2, ArgsT{T}((a, Const{T}(N))); type = Int, shape = ShapeVecT())
brusselator_f(x, y, t) = (((x - 0.3)^2 + (y - 0.6)^2) <= 0.1^2) * (t >= 1.1) * 5.0

SymbolicUtils.promote_symtype(::typeof(brusselator_f), args...) = Real

@testset "Brusselator stencil" begin
    n = 8
    @syms t::Real u(t)[1:n, 1:n]::Real v(t)[1:n, 1:n]::Real
    u = u(t)
    v = v(t)

    x = y = range(0, stop=1, length=n)
    dx = step(x)

    A = 3.4
    alpha = 10.0

    dtu = @arrayop (i, j) alpha * (u[limit2(i - 1, n), j] +
                                   u[limit2(i + 1, n), j] +
                                   u[i, limit2(j + 1, n)] +
                                   u[i, limit2(j - 1, n)] -
                                   4u[i, j]) +
                          1.0 + u[i, j]^2 * v[i, j] - (A + 1) *
                            u[i, j] + brusselator_f(x[i], y[j], t) i in 1:n j in 1:n
    dtv = @arrayop (i, j) alpha * (v[limit2(i - 1, n), j] +
                                   v[limit2(i + 1, n), j] +
                                   v[i, limit2(j + 1, n)] +
                                   v[i, limit2(j - 1, n)] -
                                   4v[i, j]) -
                          u[i, j]^2 * v[i, j] + A * u[i, j] i in 1:n j in 1:n
    lapu = @arrayop (i, j) (u[limit2(i - 1, n), j] +
                            u[limit2(i + 1, n), j] +
                            u[i, limit2(j + 1, n)] +
                            u[i, limit2(j - 1, n)] -
                            4u[i, j]) i in 1:n j in 1:n
    lapv = @arrayop (i, j) (v[limit2(i - 1, n), j] +
                            v[limit2(i + 1, n), j] +
                            v[i, limit2(j + 1, n)] +
                            v[i, limit2(j - 1, n)] -
                            4v[i, j]) i in 1:n j in 1:n
    s = brusselator_f.(x, y', t)

    st = Code.NameState()
    st.rewrites[:arrayop_eltype] = BasicSymbolic{SymReal}
    st.rewrites[:arrayop_output] = :du
    st.rewrites[u] = :u
    st.rewrites[v] = :v
    du = eval(quote
        let du = fill(Const{SymReal}(0), $n, $n), u = $(collect(u)), v = $(collect(v)), t = $t
            $(toexpr(dtu, st))
            du
        end
    end)
    @test isequal(collect(du), scalarize(dtu))

    vv = collect(v)
    uu = collect(u)
    @test isequal(scalarize(dtu), collect(1 .+ vv .* uu.^2 .- (A + 1) .* uu .+ alpha .* scalarize(lapu) .+ s))
    @test isequal(scalarize(dtv), collect(A .* uu .- uu.^2 .* vv .+ alpha .* scalarize(lapv)))
end

@testset "broadcast & scalarize" begin
    @syms A[1:5,1:3] b[1:3] t x(t)[1:4] u[1:1]
    x = x(t)
    AA = scalarize(A)
    bb = scalarize(b)
    @test isequal(scalarize(b .^ 1), bb)
    c = A * b

    @syms d[1:3] E[1:3, 1:3]
    d_vec = collect(d)
    @test d_vec' isa Adjoint{BasicSymbolic{SymReal}, Vector{BasicSymbolic{SymReal}}}
    result1 = d_vec' * E
    result2 = d_vec' * inv(E) * d_vec
    @test size(result1) == (1, 3)
    @test size(result2) == ()

    @test isequal(scalarize(sin.(x)),
        sin.([x[i] for i in 1:4]))

    @test isequal(scalarize(sin.(A .* c)[1, 1]),
        sin(A[1, 1] * (b[1] * A[1, 1] +
                       b[2] * A[1, 2] +
                       b[3] * A[1, 3])))

    @test isequal(scalarize(u + u), [2u[1]])

    @syms A[1:2, 1:2]
    test_mat = [1 2; 3 4]
    repl_dict = Dict(scalarize(A .=> test_mat))
    A2 = A^2
    A3 = A^3
    A4 = A^4
    A5 = A^5
    A6 = A^6
    A7 = A^7

    @syms i::Int j::Int k::Int l::Int m::Int n::Int

    A_ = A
    A3_ = @arrayop (i, j) A_[i, k] * A_[k, l] * A_[l, j]
    A4_ = @arrayop (i, j) A_[i, k] * A_[k, l] * A_[l, m] * A_[m, j]
    A5_ = @arrayop (i, j) A_[i, k] * A_[k, l] * A_[l, m] * A_[m, n] * A_[n, j]

    @test_broken isequal(scalarize((A*A)[k,k]), A[k, 1]*A[1, k] + A[2, k]*A[k, 2])

    # basic tests:
    @test iszero(unwrap_const(expand((scalarize(A^2) * scalarize(A))[1,1] -
                  scalarize(A^3)[1,1])))
    @testset "nested scalarize" begin
        @test isequal(unwrap_const.(substitute(scalarize(A2 ), repl_dict)), test_mat^2)
        @test isequal(unwrap_const.(substitute(scalarize(A3_), repl_dict)), test_mat^3)
        @test isequal(unwrap_const.(substitute(scalarize(A3 ), repl_dict)), test_mat^3)
        @test isequal(unwrap_const.(substitute(scalarize(A4_), repl_dict)), test_mat^4)
        @test isequal(unwrap_const.(substitute(scalarize(A4 ), repl_dict)), test_mat^4)
        @test isequal(unwrap_const.(substitute(scalarize(A5_), repl_dict)), test_mat^5)
        @test isequal(unwrap_const.(substitute(scalarize(A5 ), repl_dict)), test_mat^5)
        @test isequal(unwrap_const.(substitute(scalarize(A6 ), repl_dict)), test_mat^6)
        @test isequal(unwrap_const.(substitute(scalarize(A7 ), repl_dict)), test_mat^7)
    end

    @test isequal(scalarize(inv(A)), [inv(A)[i] for i in eachindex(A)])
end

@testset "map/mapreduce" begin
    @syms a[1:2] b[1:2, 1:2] c[1:2, 1:2, 1:2]
    @testset "$f($v)" for v in [a, b, c], f in [sum, prod]
        var = f(v)
        @test isarrayop(var)
        @test SymbolicUtils.shape(var) == ShapeVecT()
        @test symtype(var) == Number
        @test isequal(scalarize(var), f(collect(v)))
    end

    @syms a[1:8] b[1:2, 1:4]
    @test_throws AssertionError map(+, a, b)
    @test_throws AssertionError mapreduce(+, +, a, b)
end
