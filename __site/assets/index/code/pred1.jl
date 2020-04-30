# This file was generated, do not modify it. # hide
r = @rule ~x + ~~y::(ys->iseven(length(ys))) => "odd terms"

@show r(w + z + z)
@show r(w + z)