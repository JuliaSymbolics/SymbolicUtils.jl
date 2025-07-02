using SymbolicUtils, BenchmarkTools

@syms a b c d e f g h i
ex = (f + ((((g*(c^2)*(e^2)) / d - e*h*(c^2)) / b + (-c*e*f*g) / d + c*e*i) /
                 (i + ((c*e*g) / d - c*h) / b + (-f*g) / d) - c*e) / b +
            ((g*(f^2)) / d + ((-c*e*f*g) / d + c*f*h) / b - f*i) /
            (i + ((c*e*g) / d - c*h) / b + (-f*g) / d)) / d

@benchmark SymbolicUtils.fraction_iszero($ex)
