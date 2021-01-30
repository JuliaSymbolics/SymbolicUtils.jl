# This file was generated, do not modify it. # hide
@syms x y

acr = @acrule((~y)^(~n) * ~y => (~y)^(~n+1))

acr(x^2 * y * x)