using SymbolicUtils, Test
using SymbolicUtils: Term, symtype
using BenchmarkTools

function goldstein_price()
    @syms x1 x2
    f1 = x1+x2+1
    f2 = 19-14*x1+3*x1^2-14*x2+6*x1*x2+3*x2^2
    f3 = 2*x1-3*x2
    f4 = 18-32*x1+12*x1^2+48*x2-36*x1*x2+27*x2^2

    # f(x) is the Goldstein-Price function
    f = (1+f1^2*f2)*(30+f3^2*f4)
    @btime expand($f)
    f2 = f^2
    @btime expand($f2)
    f3 = f^3
    @btime expand($f3)
end
