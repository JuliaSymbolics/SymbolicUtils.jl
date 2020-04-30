# This file was generated, do not modify it. # hide
r2 = @rule ~x * +(~~ys) => sum(map(y-> ~x * y, ~~ys));

showraw(r2(2 * (w+w+α+β)))