export IRVisitor, PostOrder,
       walk_ir, transform_ir, passthrough_visitor,
       visit

"""
    IRContext

Holds contextual information during IR traversal including:
- visited: Set of visited nodes (for cycle detection)
- depth: Current traversal depth
- scope_stack: Stack of scopes for symbol resolution
- metadata: User-defined metadata
"""
mutable struct IRContext
    visited::Set{UInt64}
    depth::Int
    scope_stack::Vector{Dict{Symbol, Any}}
    metadata::Dict{Symbol, Any}
end

IRContext() = IRContext(Set{UInt64}(), 0, [Dict{Symbol, Any}()], Dict{Symbol, Any}())

function push_scope!(ctx::IRContext)
    push!(ctx.scope_stack, Dict{Symbol, Any}())
    return ctx
end

function pop_scope!(ctx::IRContext)
    pop!(ctx.scope_stack)
    return ctx
end

current_scope(ctx::IRContext) = last(ctx.scope_stack)

"""
    walk_ir(ir, visitor, [order=PostOrder()], [ctx=IRContext()])

Walk the IR structure and apply visitor at each node.

# Arguments
- `ir`: The IR node to walk (can be any CodegenPrimitive or expression)
- `visitor`: An IRVisitor that defines how to transform nodes
- `order`: Either `PreOrder()` or `PostOrder()` traversal
- `ctx`: IRContext for maintaining state during traversal

# Returns
The transformed IR structure
"""
function walk_ir(ir, visitor, order=PostOrder(), ctx=IRContext())
    ctx.depth += 1
    # result = walk_ir_postorder(ir, visitor, ctx)
    result = visit(visitor, ir, ctx)
    ctx.depth -= 1
    return result
end

"""
    IRVisitor

Abstract type for IR visitors. Subtype this and define visit methods
for the IR node types you want to transform.

# Example
```julia
struct MyVisitor <: IRVisitor end

function visit_assignment(v::MyVisitor, asgn::Assignment, ctx)
    # Your transformation logic
    return transformed_assignment
end
```
"""
abstract type IRVisitor end

# Default passthrough visitor - returns nodes unchanged
struct PassthroughVisitor <: IRVisitor end

"""
    passthrough_visitor()

Returns a visitor that passes through all nodes unchanged.
Useful as a base for selective transformations.
"""
passthrough_visitor() = PassthroughVisitor()

# Fallback for primitives (Int, Symbol, etc.)
visit(visitor::IRVisitor, node::Union{Int, Symbol, Nothing}, ctx) = node

"""
    visit_assignment(visitor, asgn::Assignment, ctx)

Visit an Assignment node. Default implementation recursively visits rhs.
"""
function visit(visitor::IRVisitor, asgn::Assignment, ctx)
    new_lhs = walk_ir(asgn.lhs, visitor, PostOrder(), ctx)
    new_rhs = walk_ir(asgn.rhs, visitor, PostOrder(), ctx)
    return Assignment(new_lhs, new_rhs)
end

"""
    visit_let(visitor, let_node::Let, ctx)

Visit a Let node. Default implementation recursively visits pairs and body.
"""
function visit(visitor::IRVisitor, let_node::Let, ctx)
    push_scope!(ctx)
    new_pairs = [walk_ir(pair, visitor, PostOrder(), ctx) for pair in let_node.pairs]
    new_body = walk_ir(let_node.body, visitor, PostOrder(), ctx)
    pop_scope!(ctx)
    return Let(new_pairs, new_body, let_node.let_block)
end

"""
    visit_func(visitor, func::Func, ctx)

Visit a Func node. Default implementation recursively visits body.
"""
function visit(visitor::IRVisitor, func::Func, ctx)
    push_scope!(ctx)
    new_args = [walk_ir(arg, visitor, PostOrder(), ctx) for arg in func.args]
    new_kwargs = [walk_ir(kw, visitor, PostOrder(), ctx) for kw in func.kwargs]
    new_body = walk_ir(func.body, visitor, PostOrder(), ctx)
    pop_scope!(ctx)
    return Func(new_args, new_kwargs, new_body, func.pre)
end

"""
    visit_makearray(visitor, ma::MakeArray, ctx)

Visit a MakeArray node. Default implementation recursively visits elements.
"""
function visit(visitor::IRVisitor, ma::MakeArray, ctx)
    new_elems = walk_ir(ma.elems, visitor, PostOrder(), ctx)
    new_similarto = walk_ir(ma.similarto, visitor, PostOrder(), ctx)
    return MakeArray(new_elems, new_similarto, ma.output_eltype)
end

"""
    visit_maketuple(visitor, mt::MakeTuple, ctx)

Visit a MakeTuple node. Default implementation recursively visits elements.
"""
function visit(visitor::IRVisitor, mt::MakeTuple, ctx)
    new_elems = [walk_ir(elem, visitor, PostOrder(), ctx) for elem in mt.elems]
    return MakeTuple(new_elems)
end

"""
    visit_destructuredargs(visitor, da::DestructuredArgs, ctx)

Visit a DestructuredArgs node. Default implementation recursively visits elements.
"""
function visit(visitor::IRVisitor, da::DestructuredArgs, ctx)
    new_elems = [walk_ir(elem, visitor, PostOrder(), ctx) for elem in da.elems]
    new_name = walk_ir(da.name, visitor, PostOrder(), ctx)
    return DestructuredArgs(new_elems, da.inds, new_name, da.inbounds, da.create_bindings)
end


# Dispatch for BasicSymbolic expressions
function visit(visitor::IRVisitor, expr::BasicSymbolic, ctx)
    if iscall(expr)
        op = operation(expr)
        args = arguments(expr)
        new_args = [walk_ir(arg, visitor, PostOrder(), ctx) for arg in args]
        # Check if any args changed
        if any(new_args[i] !== args[i] for i in eachindex(args))
            return maketerm(typeof(expr), op, new_args, metadata(expr))
        end
    end
    return expr
end

"""
    PostOrder

Traversal order marker: visit children before parent (default).
"""
struct PostOrder end

# Handle arrays and tuples
function visit(visitor, ir::AbstractArray, ctx)
    new_elems = [walk_ir(elem, visitor, PostOrder(), ctx) for elem in ir]
    # Check if any changed
    if any(new_elems[i] !== ir[i] for i in eachindex(ir))
        return new_elems
    end
    return ir
end

function visit(visitor, ir::Tuple, ctx)
    new_elems = tuple([walk_ir(elem, visitor, PostOrder(), ctx) for elem in ir]...)
    return new_elems
end

struct FunctionalVisitor{F} <: IRVisitor
    fn::F
end

# # Override all visit methods to use the function
for t in [:Assignment, :Let, :Func, :ForLoop,
        :SetArray, :MakeArray, :MakeSparseArray,
        :MakeTuple, :AtIndex, :DestructuredArgs,
        :SpawnFetch, :LiteralExpr, :BasicSymbolic]
    @eval begin
        function visit(v::FunctionalVisitor, node::$t, ctx)
            result = v.fn(node, ctx)
            # If function returns nothing, fall back to default traversal
            if result === nothing
                return visit(passthrough_visitor(), node, ctx)
            end
            return result
        end
    end
end

"""
    transform_ir(transform_fn, ir, [order=PostOrder()])

High-level function to transform IR using a function.

# Arguments
- `ir`: The IR to transform
- `transform_fn`: Function that takes (node, ctx) and returns transformed node
- `order`: PreOrder() or PostOrder()

# Example
```julia
# Remove all assignments to a specific variable
result = transform_ir(my_ir, PostOrder()) do node, ctx
    if node isa Assignment && nameof(node.lhs) == :temp
        return nothing  # Remove this assignment
    end
    return node
end
```
"""
function transform_ir(transform_fn, ir;
                    order = PostOrder(),
                    visitor = FunctionalVisitor(transform_fn))
    return walk_ir(ir, visitor, order)
end

struct Mul5Visitor <: IRVisitor end
function Code.visit(visitor::Mul5Visitor, asgn::Assignment, ctx)
    if operation(asgn.rhs) == +
        Assignment(asgn.lhs, -(arguments(asgn.rhs)...))
    else
        asgn
    end
end




