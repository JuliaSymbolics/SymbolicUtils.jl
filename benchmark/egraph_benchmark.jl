using SymbolicUtils 
using Metatheory
using SymbolicUtils: is_literal_number, isnotflat, needs_sorting, hasrepeats, egraph_simterm

# checking the type directly is faster than dynamic dispatch in type unstable code
_iszero(x) = x isa Number && iszero(x)
_isone(x) = x isa Number && isone(x)
_isinteger(x) = (x isa Number && isinteger(x)) || (symtype(x) <: Integer)
_isreal(x) = (x isa Number && isreal(x)) || (symtype(x) <: Real)


# NOTE: SHOULD NOT USE => OPERATOR!
"""
Equational rewrite rules for optimizing expressions
"""
theory = @theory a b c x y z begin
    a + (b + c) == (a + b) + c
    a * (b * c) == (a * b) * c
    x + 0 --> x
    a + b == b + a
    a - a => 0 # is it ok?
    a * b == b * a
    a * x + a * y == a*(x+y)
    -1 * a == -a
    a + (-1 * b) == a - b
    x * 1 --> x
    x * 0 --> 0
    x/x --> 1
    # fraction rules 
    x^-1 == 1/x 
    1/x * a == a/x # is this needed?
    x / (x / y) --> y
    x * (y / z) == (x * y) / z

    (a/b) + (c/b) --> (a+c)/b
    (a / b) / c == a/(b*c)
    
    # pow rules 
    a * a == a^2
    # trig functions
    sin(x)/cos(x) == tan(x)
    cos(x)/sin(x) == cot(x)
    sin(x)^2 + cos(x)^2 --> 1
    sin(2a) == 2sin(a)cos(a)
end

@syms a b c d e f g h i
ex = (f + ((((g*(c^2)*(e^2)) / d - e*h*(c^2)) / b + (-c*e*f*g) / d + c*e*i) /
                    (i + ((c*e*g) / d - c*h) / b + (-f*g) / d) - c*e) / b +
               ((g*(f^2)) / d + ((-c*e*f*g) / d + c*f*h) / b - f*i) /
               (i + ((c*e*g) / d - c*h) / b + (-f*g) / d)) / d

o = (d + (e*((c*(g + (-d*g) / d)) / (i + (-c*(h + (-e*g) / d)) / b + (-f*g) / d))) / b +
    (-f*(g + (-d*g) / d)) / (i + (-c*(h + (-e*g) / d)) / b + (-f*g) / d)) / d

optimize(ex)

egraph = SymbolicUtils.symbolicegraph(o)
params = SaturationParams(
    timeout=7, 
    simterm=egraph_simterm, 
    eclasslimit=300_000,
    printiter = true
)
@btime saturate!(egraph, theory, params)
@btime extract!(egraph, astsize; simterm=egraph_simterm)


