from sage.all import *

def generate_keys(k, n, m, order="deglex"):
    R = PolynomialRing(k, ["x%d" % i for i in range(1, n+1)] + [f'b_{l}_{i}_{j}' for l in range(m) for i in range(n-m) for j in range(n)])
    M = MatrixSpace(k, n)
    # Generate central maps.
    F = []
    for l in range(m):
        x = R.gens()
        f = 0
        for i in range(n - m):
            start_index = i
            for j in range(start_index, n):
                f += R(f'b_{l}_{i}_{j}') * x[i] * x[j]
        F.append(f)
    # Generate the secret transformation T.
    T = M.random_element()
    while not T.is_invertible():
        T = M.random_element()
    # Compose the central maps with T.
    P = [T.act_on_polynomial(f) for f in F]
    return P, F, T

def find_linear_syzygy(F, k, n, m):
    """
    Check if there exists a syzygy among the polynomials in F, i.e.,
    if there are linear polynomials L1, ..., Lm such that:
    L1 * F1 + L2 * F2 + ... + Lm * Fm = 0.

    Also constructs a system of linear equations by summing up the symbolic coefficients
    for terms with the same monomial in x1, x2, ..., xn and equating them to zero.

    Returns the list of L1, ..., Lm if a syzygy is found, otherwise returns None.
    """
    # Step 1: Define the polynomial ring for variables x1, ..., xn and a_ij
    R = PolynomialRing(k, ["x%d" % i for i in range(1, n+1)] + [f'b_{l}_{i}_{j}' for l in range(m) for i in range(n-m) for j in range(n)])
    x = R.gens()[:n]  # Get the x variables (x1, ..., xn)
    b = R.gens()[n:]  # Get the a_ij variables

    x_vars = var(["x%d" % i for i in range(1, n+1)])  # Define the variables for x1, x2, ..., xn
    b_vars = var([f'b_{l}_{i}_{j}' for l in range(m) for i in range(n-m) for j in range(n)])

    # Step 2: Create m linear polynomials L1, ..., Lm, each with unknown coefficients a_ij
    L = []
    for i in range(m):
        L_i = sum(k.random_element() * var for j, var in enumerate(x))  # Create Li = a_i0*x1 + a_i1*x2 + ...
        L.append(L_i)

    # Step 3: Set up the syzygy equation: L1 * F1 + L2 * F2 + ... + Lm * Fm = 0
    syzygy_eq = sum(L[i] * F[i] for i in range(m))
    # print("syzygy_eq")
    # print(str(syzygy_eq))

    # Step 4: Expand and collect monomials to form a system of linear equations
    def construct_linear_system_from_syzygy(eq, n, m):
        """
        Given a polynomial equation, construct a system of linear equations by summing up
        the symbolic coefficients for terms with the same monomial in x1, x2, ..., xn
        and equating them to zero.
        """
        R = PolynomialRing(k, ["x%d" % i for i in range(1, n+1)]) # Include a_ij variables
        x = R.gens()

        x_vars = var(["x%d" % i for i in range(1, n+1)])  # Define the variables for x1, x2, ..., xn
        b_vars = var([f'b_{l}_{i}_{j}' for l in range(m) for i in range(n-m) for j in range(n)])


        # Step 2: Parse the equation string into a symbolic expression and simplify
        polynomial = SR(str(eq)).expand()  # Expand the equation to combine like terms

        # Step 3: Extract terms and group them by monomials in x's
        monomial_dict = {}

        # Iterate through the terms of the expanded polynomial
        for term in polynomial.operands():
            # Separate coefficient (containing a_ij, sign, and weights) from monomial in x's
            # coeff = term.coefficient(x_vars) # This line caused the error
            # Calculate the coefficient by setting all x variables to 1
            coeff = term.subs({x:1 for x in x_vars})
            monomial_part = term/coeff
            monomial_part = monomial_part.expand()  # Ensure it's in canonical form

            # Add the coefficient to the corresponding monomial (summing them up if monomial repeats)
            if monomial_part not in monomial_dict:
                monomial_dict[monomial_part] = coeff
            else:
                monomial_dict[monomial_part] += coeff

        # Step 4: Construct the system of linear equations by equating the coefficients to zero
        linear_system = []
        for monomial, coeff in monomial_dict.items():
            equation = coeff == 0  # Set the sum of coefficients to zero
            linear_system.append(equation)
        return linear_system
        
    # print("syzygy_eq")
    # print(syzygy_eq)            
    
    # Step 5: Construct the linear system from the syzygy equation
    linear_system = construct_linear_system_from_syzygy(syzygy_eq, n, m)

    R = PolynomialRing(k, ["x%d" % i for i in range(1, n+1)] + [f'b_{l}_{i}_{j}' for l in range(m) for i in range(n-m) for j in range(n)])

    # print("linear_system")
    # print(linear_system)

    # Step 6: Solve the system of equations for the unknown coefficients a_ij
    solutions = solve(linear_system, b_vars)
    # print("solutions")
    # print(str(solutions))

    def is_non_trivial_solution(solution):
      """
      Checks if a solution to a system of equations is trivial (all variables are zero).

      Args:
        solutions (list): A list of solutions, where each solution is a list of equations.

      Returns:
        bool: True if the solution is trivial, False otherwise.
      """
      for equation in solution:
        if equation.rhs() != 0: # Access the right-hand side of the equation to check the value
          return True
      return False

    for solution in solutions:
      if is_non_trivial_solution(solution):
        # print("is_non_trivial_solution")
        return solution_to_quadratic_polynomials(solution, x_vars, m, n)  # Return the first non-trivial solution
    # print("not is_non_trivial_solution")
    return None  # No non-trivial solution found


    # Step 7: Check if a solution exists
    # if solutions:
    #     # Construct the linear polynomials L1, ..., Lm from the solution
    #     L_solution = []
    #     for i in range(m):
    #         L_i_solution = sum(solutions[R(f'a_{i}_{j}')] * x[j] for j in range(n))
    #         L_solution.append(L_i_solution)
    #     return L_solution  # Return the linear polynomials (the syzygy)
    # else:
    #     return None  # No syzygy found

def generate_keys_with_syzygy(k, n, m, order="deglex"):
    """
    Continuously generate UOV keys using generate_keys() and check for linear syzygies.
    If a syzygy is found, return the linear polynomials L1, ..., Lm.
    """
    counter = 0
    while True:
        # print(counter)
        # Generate UOV keys using the generate_keys function
        P, F, T = generate_keys(k, n, m, order)

        # Check if a linear syzygy exists in the generated keys
        L = find_linear_syzygy(P, k, n, m)

        counter += 1

        if L != None:
            # If a syzygy is found, return the linear polynomials L1, ..., Lm
            return L, P, F, T

def solution_to_quadratic_polynomials(solution, x_vars, m, n):
    """
    Transform the solution coefficients into the corresponding quadratic polynomials.

    Args:
    solution (list): A list of equations representing the solution, e.g.,
                     [a_0_0 == r1, a_0_1 == 0, a_0_2 == r1, ...]
    x_vars (list): A list of variables (x1, x2, ..., xn) corresponding to the quadratic polynomials.
    m (int): The number of quadratic polynomials.
    n (int): The number of x variables.

    Returns:
    list: A list of quadratic polynomials corresponding to the solution.
    """
    # Initialize an empty list to store the quadratic polynomials
    quadratic_polynomials = []

    # Iterate over each quadratic polynomial L_i
    for l in range(m):
        quadratic_poly = 0  # Start with a zero polynomial for L_i
        for i in range(n-m):
            # Iterate over each x_j variable and the corresponding coefficient a_i_j
            for j in range(n):
                # Extract the coefficient a_i_j from the solution
                coeff = None
                for eq in solution:
                    if eq.lhs() == var(f'b_{l}_{i}_{j}'):
                        coeff = eq.rhs()  # Get the right-hand side value (the coefficient)
                        break

                # Add the term coeff * x_j to the quadratic polynomial (if coeff is not zero)
                if coeff != 0:
                    quadratic_poly += coeff * x_vars[i] * x_vars[j]

        # Add the constructed quadratic polynomial to the list
        quadratic_polynomials.append(quadratic_poly)

    return quadratic_polynomials



# # Example usage
k = GF(2)  # Finite field (can be modified)
n = 5  # Number of variables
m = 3  # Number of polynomials
x_vars = var(["x%d" % i for i in range(1, n+1)])
R = PolynomialRing(k, ["x%d" % i for i in range(1, n + 1)], order="deglex")

L, P, F, T = generate_keys_with_syzygy(k, n, m)

print("Linear Syzygies Found: ", L)
print("Public Key: ", [poly_to_matrix(p) for p in P])
print("Public Key: ", P)
print("Private Key: ", F)
print("Private Key: ", [poly_to_matrix(f) for f in F])
print("Linear Transformation: ", T)