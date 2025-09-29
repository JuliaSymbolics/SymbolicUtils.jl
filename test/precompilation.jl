using SnoopCompileCore, SymbolicUtils, AbstractTrees

syms_inf = @snoop_inference @syms x y
@syms x y z
add_inf = @snoop_inference x + y
sub_inf = @snoop_inference x - y
neg_inf = @snoop_inference -x
mul_inf = @snoop_inference x * y
coeff_inf = @snoop_inference 2x
div_inf = @snoop_inference x / y
const_div_inf = @snoop_inference x / 5
pow_inf = @snoop_inference x ^ y
print(devnull, Val{5}())
const_pow_inf = @snoop_inference x ^ 5
expr = x + sin(y) * z
rules = Dict(x => y)
fold = Val{false}()
subs_inf = @snoop_inference substitute(expr, rules; fold)

using SnoopCompile

@testset "$name" for (name, inf) in [
    ("syms", syms_inf),
    ("add", add_inf),
    ("sub", sub_inf),
    ("neg", neg_inf),
    ("mul", mul_inf),
    ("coeff", coeff_inf),
    ("div", div_inf),
    ("const_div", const_div_inf),
    ("pow", pow_inf),
    ("const_pow", const_pow_inf),
    ("substitute", subs_inf)
]
    @test isempty(staleinstances(inf))
    # `setindex!` on TaskLocalValue doesn't infer (COMPARE_FULL)
    if inf === subs_inf
        @test treesize(inf) == 21
    else
        @test isempty(children(inf))
    end
end

