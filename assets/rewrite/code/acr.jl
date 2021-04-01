# This file was generated, do not modify it. # hide
@syms x y z

acr = @acrule((~a)^(~x) * (~a)^(~y) => (~a)^(~x + ~y))

acr(x^y * x^z)