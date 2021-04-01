# This file was generated, do not modify it. # hide
@syms a b c d

r = @rule ~x + ~~y::(ys->iseven(length(ys))) => "odd terms";

@show r(a + b + c + d)
@show r(b + c + d)
@show r(b + c + b)
@show r(a + b)