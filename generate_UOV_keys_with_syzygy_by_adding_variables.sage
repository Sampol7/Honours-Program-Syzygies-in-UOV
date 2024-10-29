from sage.all import *
import random

def generate_keys(k, n, m, order="deglex"):
    R = PolynomialRing(k, ["x%d" % i for i in range(1,n+1)], order=order)
    M = MatrixSpace(k, n)
    # Generate central maps.
    F = []
    for i in range(m):
        x = R.gens()
        f = 0
        for i in range(n - m):
            start_index = i
            for j in range(start_index, n):
                f += k.random_element() * x[i] * x[j]
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
    R = PolynomialRing(k, ["x%d" % i for i in range(1, n+1)] + [f'a_{i}_{j}' for i in range(m) for j in range(n)])
    x = R.gens()[:n]  # Get the x variables (x1, ..., xn)
    a = R.gens()[n:]  # Get the a_ij variables

    x_vars = var(["x%d" % i for i in range(1, n+1)])  # Define the variables for x1, x2, ..., xn
    a_vars = var([f'a_{i}_{j}' for i in range(m) for j in range(n)])

    # Step 2: Create m linear polynomials L1, ..., Lm, each with unknown coefficients a_ij
    L = []
    L_coeffs = []
    for i in range(m):
        L_i = sum(R(f'a_{i}_{j}') * var for j, var in enumerate(x))  # Create Li = a_i0*x1 + a_i1*x2 + ...
        L.append(L_i)
        L_coeffs.extend([R(f'a_{i}_{j}') for j in range(n)])  # Collect a_ij variables as unknowns

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
        a_vars = var([f'a_{i}_{j}' for i in range(m) for j in range(n)])


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

    # Step 5: Construct the linear system from the syzygy equation
    linear_system = construct_linear_system_from_syzygy(syzygy_eq, n, m)

    R = PolynomialRing(k, ["x%d" % i for i in range(1, n+1)] + [f'a_{i}_{j}' for i in range(m) for j in range(n)])

    # Step 6: Solve the system of equations for the unknown coefficients a_ij
    solutions = solve(linear_system, a_vars)
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
        return solution_to_linear_polynomials(solution, x_vars, m, n)  # Return the first non-trivial solution
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

def generate_keys_with_syzygy(k, n, m, random_ratio=0.7, order="deglex"):
    """
    Generate UOV keys and ensure they have linear syzygies. Randomly generate part of the coefficients,
    and solve for the remaining ones using a syzygy equation.
    """
    R = PolynomialRing(k, ["x%d" % i for i in range(1, n+1)], order=order)
    M = MatrixSpace(k, n)

    L = None
    while L is None:
        # Coefficients of polynomials F, either random or variables
        def random_or_variable(i, j):
            return k.random_element() if random.random() < random_ratio else var(f'b_{i}_{j}')

        # Generate central polynomials F with random coefficients and variables
        F = []
        for i in range(m):
            x = R.gens()
            f = 0
            for i in range(n - m):
                start_index = i
                for j in range(start_index, n):
                    f += random_or_variable(i, j) * x[i] * x[j]
            F.append(f)

        # Extend the ring to include a_ij variables
        R_ext = PolynomialRing(k, ["x%d" % i for i in range(1, n+1)] + [f'a_{i}_{j}' for i in range(m) for j in range(n)])
        x = R_ext.gens()[:n]  # Get the x variables
        a = R_ext.gens()[n:]  # Get the a_ij variables

        # Step 2: Create m linear polynomials L1, ..., Lm, each with unknown coefficients a_ij
        L = []
        L_coeffs = []
        for i in range(m):
            L_i = sum(R_ext(f'a_{i}_{j}') * var for j, var in enumerate(x))  # Create Li = a_i0*x1 + a_i1*x2 + ...
            L.append(L_i)
            L_coeffs.extend([R_ext(f'a_{i}_{j}') for j in range(n)])  # Collect a_ij variables as unknowns

        # Step 3: Set up the syzygy equation: L1 * F1 + L2 * F2 + ... + Lm * Fm = 0
        syzygy_eq = sum(L[i] * F[i] for i in range(m))

        # Step 4: Expand and collect monomials to form a system of linear equations
        linear_system = construct_linear_system_from_syzygy(syzygy_eq, n, m)

        # Step 5: Solve the system of equations for the unknown coefficients a_ij and b_ij
        a_vars = var([f'a_{i}_{j}' for i in range(m) for j in range(n)])
        b_vars = var([f'b_{i}_{j}' for i in range(m) for j in range(n)])

        solutions = solve(linear_system, a_vars + b_vars)

        def is_non_trivial_solution(solution):
            """
            Checks if a solution to a system of equations is trivial (all variables are zero).
            """
            for equation in solution:
                if equation.rhs() != 0:  # Check if the right-hand side is non-zero
                    return True
            return False

        for solution in solutions:
            if is_non_trivial_solution(solution):
                L = solution_to_linear_polynomials(solution, x, m, n)  # Return the first non-trivial solution
                break
        else:
            L = None  # No non-trivial solution found

    # Substitute solutions into F to finalize the key
    F_with_substituted_solutions = substitute_solutions_in_F(F, solutions, b_vars)

    # Generate the secret transformation T
    T = M.random_element()
    while not T.is_invertible():
        T = M.random_element()

    # Compose the central polynomials with T
    P = [T.act_on_polynomial(f) for f in F_with_substituted_solutions]

    return L, P, F_with_substituted_solutions, T


def construct_linear_system_from_syzygy(eq, n, m):
    """
    Given a syzygy equation, construct a system of linear equations by collecting the coefficients
    of each monomial and equating them to zero.
    """
    R = PolynomialRing(k, ["x%d" % i for i in range(1, n+1)])
    x_vars = var(["x%d" % i for i in range(1, n+1)])

    polynomial = SR(str(eq)).expand()

    monomial_dict = {}
    for term in polynomial.operands():
        coeff = term.subs({x: 1 for x in x_vars})
        monomial_part = term / coeff
        monomial_part = monomial_part.expand()

        if monomial_part not in monomial_dict:
            monomial_dict[monomial_part] = coeff
        else:
            monomial_dict[monomial_part] += coeff

    linear_system = [coeff == 0 for coeff in monomial_dict.values()]
    return linear_system


def substitute_solutions_in_F(F, solutions, b_vars):
    """
    Substitute the solutions for the b_ij variables back into the polynomials F.
    """
    substitutions = {b: sol.rhs() for b, sol in zip(b_vars, solutions)}
    return [f.subs(substitutions) for f in F]


def solution_to_linear_polynomials(solution, x_vars, m, n):
    """
    Transform the solution coefficients into the corresponding linear polynomials.

    Args:
    solution (list): A list of equations representing the solution, e.g.,
                     [a_0_0 == r1, a_0_1 == 0, a_0_2 == r1, ...]
    x_vars (list): A list of variables (x1, x2, ..., xn) corresponding to the linear polynomials.
    m (int): The number of linear polynomials.
    n (int): The number of x variables.

    Returns:
    list: A list of linear polynomials corresponding to the solution.
    """
    # Initialize an empty list to store the linear polynomials
    linear_polynomials = []

    # Iterate over each linear polynomial L_i
    for i in range(m):
        linear_poly = 0  # Start with a zero polynomial for L_i

        # Iterate over each x_j variable and the corresponding coefficient a_i_j
        for j in range(n):
            # Extract the coefficient a_i_j from the solution
            coeff = None
            for eq in solution:
                if eq.lhs() == var(f'a_{i}_{j}'):
                    coeff = eq.rhs()  # Get the right-hand side value (the coefficient)
                    break

            # Add the term coeff * x_j to the linear polynomial (if coeff is not zero)
            if coeff != 0:
                linear_poly += coeff * x_vars[j]

        # Add the constructed linear polynomial to the list
        linear_polynomials.append(linear_poly)

    return linear_polynomials

def verify_syzygy(L, F, x_vars):
    """
    Verify if L1 * F1 + L2 * F2 + ... + Lm * Fm = 0.

    Args:
    L (list): List of linear polynomials L1, ..., Lm.
    F (list): List of private key polynomials F1, ..., Fm.
    x_vars (list): List of variables (x1, x2, ..., xn).

    Returns:
    bool: True if L1 * F1 + L2 * F2 + ... + Lm * Fm = 0, False otherwise.
    """
    # Ensure that the lengths of L and F are the same
    if len(L) != len(F):
        raise ValueError("Length of L and F must be the same")

    # Compute the sum L1 * F1 + L2 * F2 + ... + Lm * Fm
    syzygy_sum = sum(L[i] * F[i] for i in range(len(L)))

    # Simplify the result
    # syzygy_sum = syzygy_sum.simplify_full()

    if syzygy_sum == 0:
        return True
    else:
        return False

def verify_syzygy_symbolically(L, F, x_vars):
    """
    Verify if L1 * F1 + L2 * F2 + ... + Lm * Fm = 0.

    Args:
    L (list): List of linear polynomials L1, ..., Lm.
    F (list): List of private key polynomials F1, ..., Fm.
    x_vars (list): List of variables (x1, x2, ..., xn).

    Returns:
    bool: True if L1 * F1 + L2 * F2 + ... + Lm * Fm = 0, False otherwise.
    """
    # Ensure that the lengths of L and F are the same
    if len(L) != len(F):
        raise ValueError("Length of L and F must be the same")

    # Compute the sum L1 * F1 + L2 * F2 + ... + Lm * Fm
    syzygy_sum = sum(SR(str(L[i])) * SR(str(F[i])) for i in range(len(L)))

    # Simplify the result
    syzygy_sum = syzygy_sum.simplify_full()

    if syzygy_sum == 0:
        return True
    else:
        return False

def symbolic_to_polynomial(symbolic_expressions, R):
    """
    Transforms a list of symbolic expressions to a list of elements in the specified polynomial ring,
    substituting each symbolic variable starting with 'r' with 1.

    Args:
        symbolic_expressions (list): List of symbolic expressions.
        R (PolynomialRing): The target polynomial ring.

    Returns:
        list: A list of polynomials in the polynomial ring with variables substituted by 1.
    """

    substituted_expressions = []
    
    for expr in symbolic_expressions:
        # Check if the expression is symbolic (not a constant integer)
        if hasattr(expr, 'variables'):
            # Substitute variables starting with 'r' with 1
            substituted_expressions.append(expr.subs({var: 1 for var in expr.variables() if str(var).startswith('r')}))
        else:
            # Directly append the integer/constant term
            substituted_expressions.append(expr)

    # Convert the substituted expressions into elements of the polynomial ring
    polynomials = [R(expr) for expr in substituted_expressions]
    
    return polynomials

def apply_transformation(T, L, R):
    """
    Toepassing van een lineaire transformatie T op een lijst van lineaire polynomen L(x).
    
    Args:
    T (matrix): Matrix van de lineaire transformatie (van grootte n x n).
    L (list): Lijst van lineaire polynomen in de vorm van x-variabelen.
    R (PolynomialRing): De polynoomring waarin de polynomen zijn gedefinieerd.
    
    Returns:
    list: Een nieuwe lijst van lineaire polynomen na toepassing van T op de variabelen van L(x).
    """
    x_vars = R.gens()  # Haal de variabelen (x1, x2, ..., xn) uit de polynoomring
    n = len(x_vars)    # Aantal variabelen

    # Stap 1: Bereken de beelden van de x-variabelen onder de transformatie T
    transformed_vars = [sum(T[i, j] * x_vars[j] for j in range(n)) for i in range(n)]

    # Stap 2: Vervang elke x_i in L(x) door T(x_i)
    transformed_L = []
    for poly in L:
        new_poly = poly.subs({x_vars[i]: transformed_vars[i] for i in range(n)})
        transformed_L.append(new_poly)

    return transformed_L


# # Example usage
k = GF(2)  # Finite field (can be modified)
n = 5  # Number of variables
m = 3  # Number of polynomials
x_vars = var(["x%d" % i for i in range(1, n+1)])
R = PolynomialRing(k, ["x%d" % i for i in range(1, n + 1)], order="deglex")

L, P, F, T = generate_keys_with_syzygy(k, n, m)
print("Linear Syzygies Found: ", L)
print("Public Key: ", P)
print("Private Key: ", F)
print("Linear Transformation: ", T)
print("Syzygy Verifies Symbolically: ", verify_syzygy_symbolically(L, F, x_vars))
print("Syzygy Verifies Symbolically: ", verify_syzygy_symbolically(L, P, x_vars))

print("Linear Syzygies Found: ", symbolic_to_polynomial(L,R))
print("Syzygy Verifies Over R: ", verify_syzygy(symbolic_to_polynomial(L,R), F, x_vars))
print("Syzygy Verifies Over R: ", verify_syzygy(symbolic_to_polynomial(L,R), P, x_vars))
print("Syzygy Verifies Over R: ", verify_syzygy(apply_transformation(T, symbolic_to_polynomial(L,R), R), P, x_vars)) #public syzygy is equal to L(T(x))