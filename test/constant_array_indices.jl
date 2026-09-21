using SymbolicUtils, Test
using SymbolicUtils: iscall, operation, unwrap_const

@testset "Substitution preserves symbolic indices into constant arrays" begin
    @syms index::Int replacement::Int
    for values in (collect(1:4), collect(1.0:4.0))
        expression = term(getindex, values, index; type = eltype(values))
        replaced = substitute(expression, Dict(index => replacement))
        @test iscall(replaced)
        @test isequal(operation(replaced), getindex)
        @test unwrap_const(substitute(replaced, Dict(replacement => 2))) == values[2]
        @test unwrap_const(substitute(expression, Dict(index => 3))) == values[3]
    end
    values = [1 3; 2 4]
    expression = term(getindex, values, index, 2; type = Int)
    replaced = substitute(expression, Dict(index => replacement))
    @test unwrap_const(substitute(replaced, Dict(replacement => 1))) == 3
    @test unwrap_const(substitute(replaced, Dict(replacement => 2))) == 4
    nested = substitute(expression + 1, Dict(index => replacement))
    @test unwrap_const(substitute(nested, Dict(replacement => 1))) == 4
    @test unwrap_const(substitute(nested, Dict(replacement => 2))) == 5
end
