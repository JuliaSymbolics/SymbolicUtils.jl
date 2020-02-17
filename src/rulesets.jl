
BASIC_NUMBER_RULES = let
    [@rule(~x - ~y => ~x + (-1 * ~y)),
     @rule(~x / ~y => ~x * pow(~y, -1)),
     #@rule(*(~~x, *(~~y), ~~z) => *((~~x)..., (~~y)..., (~~z)...)),
     @rule(*(~~x::isnotflat(*)) => flatten_term(*, ~~x)),
     @rule(*(~~x::!(issortedₑ)) => sort_args(*, ~~x)),
     @rule(*(~a::isnumber, ~b::isnumber, ~~x) => *(~a * ~b, (~~x)...)),

     #@rule(+(~~x, +(~~y), ~~z) => +((~~x)..., (~~y)..., (~~z)...)),
     @rule(+(~~x::isnotflat(+)) => flatten_term(+, ~~x)),
     @rule(+(~~x::!(issortedₑ)) => sort_args(+, ~~x)),
     @rule(+(~a::isnumber, ~b::isnumber, ~~x) => +((~~x)..., ~a + ~b)),

     @rule(+(~~a, *(~~x), *(~β::isnumber, ~~x), ~~b) =>
           +((~~a)..., *(1 + ~β, (~x)...), (~b)...)),
     @rule(+(~~a, *(~α::isnumber, ~x), ~~b, ~x, ~~c) =>
           +((~~a)..., *(+(~α+1), ~x), (~~b)..., (~~c)...)),
     @rule(+(~~a, *(~α::isnumber, ~~x), *(~β::isnumber, ~~x), ~~b) =>
           +((~~a)..., *(~α + ~β, (~x)...), (~b)...)),

     # group stuff
     @rule(^(*(~~x), ~y) => *(map(a->pow(a, ~y), ~~x)...)),
     @rule(*(~~x, ^(~y, ~n), ~y, ~~z) => *((~~x)..., ^(~y, ~n+1), (~~z)...)),
     @rule(*(~~a, ^(~x, ~e1), ^(~x, ~e2), ~~b) =>
           *((~~a)..., ^(~x, (~e1 + ~e2)), (~b)...)),
     @rule((((~x)^(~p))^(~q)) => (~x)^((~p)*(~q))),
     @rule(+(~~x::hasrepeats) => +(merge_repeats(*, ~~x)...)),
     @rule(*(~~x::hasrepeats) => *(merge_repeats(^, ~~x)...)),

     @rule(*(~z::_iszero, ~~x) => ~z),

     # remove the idenitities
     @rule(*(~z::_isone, ~~x::(!isempty)) => *((~~x)...)),
     @rule(+(~z::_iszero, ~~x::(!isempty)) => +((~~x)...)),
     @rule(^(~x, ~z::_iszero) => 1),
     @rule(^(~x, ~z::_isone) => ~x),
    ]
end

multiple_of(x, tol=1e-10) = y -> (y isa Number) && abs(y % x) < 1e-10

using MacroTools: postwalk, @capture

"""
    @repeat foo => (f1, f2, f3) @rule foo(~x) => foo(~x + 1)
results in
    [@rule f1(~x) => f1(~x + 1)
     @rule f2(~x) => f2(~x + 1)
     @rule f3(~x) => f3(~x + 1)]

Automatically unpacks if used inside an array.


This can probably eventually be implemented using SymbolicUtils itself instead of macrotools
"""
macro repeat(fmap, rule) 
    @capture(fmap, f_ => fs_)
    esc(Expr(:vect, map(fout -> postwalk(x -> x == f ? fout : x, rule), fs.args)...))
end

TRIG_RULES = let
    [@repeat(f => (sin, cos, tan),
             [@rule f(~~x + ~y::multiple_of(2π) + ~~z) => f(+(~~x..., ~~z...))
       
              @rule f(~~x + ~y::multiple_of(2π) * ~n::oftype(Integer) + ~~z) => f(+(~~x..., ~~z...))
              @rule f(~~x + ~n::oftype(Integer) * ~y::multiple_of(2π) + ~~z) => f(+(~~x..., ~~z...)) # make multiplication commute

              @rule f(~~x + ~y::multiple_of(2π) * ~n::oftype(Integer) + ~~z) => f(+(~~x..., ~~z...)) # reverse addition order
              @rule f(~~x + ~n::oftype(Integer) * ~y::multiple_of(2π) + ~~z) => f(+(~~x..., ~~z...))]...)
     
     @rule ~~a + sin(~x)^2 + ~~b + cos(~x)^2 + ~~c => +(~~a..., one(~x), ~~b..., ~~c...)
     @rule ~~a + cos(~x)^2 + ~~b + sin(~x)^2 + ~~c => +(~~a..., one(~x), ~~b..., ~~c...)
     ]
end
