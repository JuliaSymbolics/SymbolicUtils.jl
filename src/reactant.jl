using Revise, BenchmarkTools

using SymbolicUtils, SymbolicUtils.Code
using LinearAlgebra
using Preferences, UUIDs
using MPI
MPI.Init()


Preferences.set_preferences!(
    UUID("3c362404-f566-11ee-1572-e11a4b42c853"),
    "xla_runtime" => "IFRT"
    # "xla_runtime" => "PJRT"
)

# using Zygote
# using Enzyme
using Reactant
Reactant.set_default_backend("cpu")
Reactant.Distributed.initialize()


@syms A[1:2, 1:2] B[1:2, 1:2] C[1:2, 1:2]

eq = A * B + C

func_expr = Func([A, B, C], [], eq)
f = eval(toexpr(func_expr))

# reactant_thetech = Reactant.to_rarray(thetech2)
# reactant_thetech_dup = Reactant.to_rarray(thetech2)

# reactant_u0ps = Reactant.to_rarray(batch.u0ps)
# reactant_ts_reshaped = Reactant.to_rarray(batch.ts_reshaped)

# f2 = @compile reactant_thetech(reactant_u0ps, reactant_ts_reshaped)


# Enzyme.gradient(Reverse, Const(goo), Const(thetech), batch.u0ps, batch.ts_reshaped)

f(rand(2, 2), rand(2, 2), rand(2, 2))

N = 128
a = rand(N, N)
b = rand(N, N)
c = rand(N, N)

a_reac = Reactant.to_rarray(a)
b_reac = Reactant.to_rarray(b)
c_reac = Reactant.to_rarray(c)

f2 = @compile f(a_reac, b_reac, c_reac)

f2(a_reac, b_reac, c_reac)

@btime $f($a, $b, $c);
@btime $f2($a_reac, $b_reac, $c_reac);

function f_naive(A, B, C)
    A * B + C
end

@btime f_naive($a, $b, $c);

f_naive_reac = @compile f_naive(a_reac, b_reac, c_reac)

@btime $f_naive_reac($a_reac, $b_reac, $c_reac);


eq = C + (A * B + C)
func_expr = Func([A, B, C],[], eq)
toexpr(func_expr)