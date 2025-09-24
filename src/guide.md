  1. Create Symbolic Variables with Type Information                                                                                                            
                                                                                                                                                                
  using SymbolicUtils                                                                                                                                           
                                                                                                                                                                
  # Create variables with specific types                                                                                                                        
  @syms x::Real y::Complex z::Integer                                                                                                                           
                                                                                                                                                                
  # For arrays with shapes and types                                                                                                                            
  @syms A[1:3, 1:3]::Matrix{Float64} b[1:3]::Vector{Float64}                                                                                                    
                                                                                                                                                                
  2. Create and Simplify System of Equations                                                                                                                    
                                                                                                                                                                
  # Create a system of equations                                                                                                                                
  eq1 = x + 2*y - 5                                                                                                                                             
  eq2 = 3*x - y + z - 10                                                                                                                                        
  eq3 = A*b + x  # Mixed symbolic array operations                                                                                                              
                                                                                                                                                                
  # Store as vector                                                                                                                                             
  equations = [eq1, eq2, eq3]                                                                                                                                   

  # Simplify each equation
  simplified_eqs = map(simplify, equations)

  3. Extract Type Information

  # Get type information for variables and expressions
  function get_type_info(expr)
      return (
          expr = expr,
          symtype = SymbolicUtils.symtype(expr),
          shape = SymbolicUtils.shape(expr),
          metadata = SymbolicUtils.metadata(expr)
      )
  end

  # Apply to your system
  type_info = map(get_type_info, simplified_eqs)


4. Access IR Form Directly

  The BasicSymbolic objects ARE the IR form. You can inspect them:

  # Check if it's a call (compound expression)
  iscall(eq1)  # true if it's an operation like +, -, etc.

  # Get operation and arguments
  if iscall(eq1)
      op = operation(eq1)      # The function/operator
      args = arguments(eq1)    # The operands
  end

  # Get variables in the expression
  function get_variables(expr)
      vars = Set()
      if issym(expr)
          push!(vars, expr)
      elseif iscall(expr)
          for arg in arguments(expr)
              union!(vars, get_variables(arg))
          end
      end
      return vars
  end


    5. Complete Example                                                                                                                                           
                                                                                                                                                                
  Here's a complete example based on your codebase:                                                                                                             
                                                                                                                                                                
  using SymbolicUtils                                                                                                                                           
  using SymbolicUtils.Code                                                                                                                                      
                                                                                                                                                                
  # Create symbolic system with types                                                                                                                           
  @syms x::Real y::Real z::Integer                                                                                                                              
  @syms A[1:2, 1:2]::Matrix{Float64} b[1:2]::Vector{Float64}

  # Create system of equations
  eqs = [
      x + 2*y - 5,           # Linear equation
      x^2 + y^2 - 1,         # Nonlinear equation  
      A*b + [x, y] - [1, 2]  # Matrix equation
  ]

  # Simplify the system (this operates on IR)
  simplified_system = map(simplify, eqs)

  # Extract complete information
  function analyze_equation(eq, idx)
      println("Equation $idx: $eq")
      println("  Type: $(SymbolicUtils.symtype(eq))")
      println("  Shape: $(SymbolicUtils.shape(eq))")

      if iscall(eq)
          println("  Operation: $(operation(eq))")
          println("  Arguments: $(arguments(eq))")
      end

      # Get all variables
      vars = get_variables(eq)
      println("  Variables:")
      for var in vars
          println("    $var :: $(SymbolicUtils.symtype(var))")
          if haskey(var, :shape)
              println("      Shape: $(SymbolicUtils.shape(var))")
          end
      end
      println()
  end

  # Analyze each equation
  for (i, eq) in enumerate(simplified_system)
      analyze_equation(eq, i)
  end

  Key Functions for IR Analysis:

  - simplify(expr): Simplifies expressions
  - SymbolicUtils.symtype(expr): Gets the Julia type
  - SymbolicUtils.shape(expr): Gets array dimensions
  - iscall(expr): Checks if compound expression
  - operation(expr): Gets the operator/function
  - arguments(expr): Gets the operands
  - issym(expr): Checks if atomic symbol
  - metadata(expr): Gets attached metadata

  The IR form in SymbolicUtils is the BasicSymbolic objects themselves - they contain all the structural and type information you need for analysis and code
   generation.
