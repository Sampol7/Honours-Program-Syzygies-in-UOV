from sage.all import *
import time


# poly_to_matrix takes a homogeneous polynomial f of degree two and returns a
# matrix corresponding to the quadratic form f. When characteristic of k is
# odd, the returned matrix is symmetric, provided the flag is set to True.
def poly_to_matrix(f, symmetric=True):
    assert f.is_homogeneous() and f.degree() == 2, "f is not homogeneous"
    R = f.parent()
    k = R.base_ring()
    n = len(R.gens())
    rows = []
    for i in range(n):
        row = [0] * n
        for j in range(i, n):
            m = R.gen(i) * R.gen(j)
            c = f.monomial_coefficient(m)
            row[j] = c
        rows.append(row)
    Q = matrix(k, rows)
    if symmetric and k.characteristic() != 2:
        Q = (Q + Q.transpose()) / 2
    # The symmetric matrix for fields of characteristic 2 is defined by
    # Q = Q + Q.transpose(), but the operations of poly_to_matrix and
    # matrix_to_poly become incompatible. So we only return symmetric
    # matrices for fields of odd characteristic for now.
    return Q

# is_central_map returns true if all elements of the specified list of
# matrices Q have zero submatrix corresponding to the oil variables.
def is_central_map(F, m):
    Q = [poly_to_matrix(f) for f in F]
    for M in Q:
        n, _ = M.dimensions()
        if not M.submatrix(n-m, n-m).is_zero():
            return False
    return True



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
        
    # print("syzygy_eq")
    # print(syzygy_eq)            
    
    # Step 5: Construct the linear system from the syzygy equation
    linear_system = construct_linear_system_from_syzygy(syzygy_eq, n, m)

    R = PolynomialRing(k, ["x%d" % i for i in range(1, n+1)] + [f'a_{i}_{j}' for i in range(m) for j in range(n)])

    # print("linear_system")
    # print(linear_system)

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
                    print(coeff)
                    break

            # Add the term coeff * x_j to the linear polynomial (if coeff is not zero)
            if coeff != 0:
                linear_poly += coeff * x_vars[j]

        # Add the constructed linear polynomial to the list
        linear_polynomials.append(linear_poly)

    return linear_polynomials



def verify_syzygy(L, F):
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


def symbolic_to_polynomial2(symbolic_expressions, R, k):
    """
    Transforms a list of symbolic expressions to a list of elements in the specified polynomial ring,
    substituting each symbolic variable starting with 'r' with a consistent random element in the field k.

    Args:
        symbolic_expressions (list): List of symbolic expressions.
        R (PolynomialRing): The target polynomial ring.
        k (FiniteField): The finite field from which random elements will be drawn.

    Returns:
        list: A list of polynomials in the polynomial ring with 'r' variables substituted by random field elements.
    """
    all_zero=True
    while all_zero:
        random_replacements = {}  # Dictionary to store consistent random replacements for 'r' variables
        substituted_expressions = []
        print(symbolic_expressions)
        for expr in symbolic_expressions:
            if hasattr(expr, 'variables'):
                # Create a substitution dictionary for variables starting with 'r'
                substitutions = {}
                for var in expr.variables():
                    var_str = str(var)
                    if var_str.startswith('r'):
                        if var_str not in random_replacements:
                            random_value = int(k.random_element())
                            random_replacements[var_str] = random_value  # Assign field element (can be 0)
                        substitutions[var] = random_replacements[var_str]
                
                # Substitute the 'r' variables with their corresponding random values
                substituted_expr = expr.subs(substitutions)
                
                # Explicitly check for zero inverses or problematic terms before converting to a polynomial
                try:
                    substituted_expressions.append(substituted_expr)
                except ZeroDivisionError as e:
                    print(f"ZeroDivisionError for expression {expr}: {e}")
                    return [0] * len(symbolic_expressions)  # Skip problematic expression for now, or handle accordingly
            else:
                substituted_expressions.append(expr)

        #if not any(expr == 0 for expr in substituted_expressions):
        all_zero=False  # Restart if all replacements are zero
    
    # Convert the substituted expressions into elements of the polynomial ring
    polynomials = []
    for expr in substituted_expressions:
        try:
            polynomials.append(R(expr))  # Attempt to create polynomial, but catch any issues
        except ZeroDivisionError as e:
            print(f"ZeroDivisionError when converting to polynomial: {e}")
            return [0] * len(symbolic_expressions)  # Skip problematic expressions or handle them as necessary
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





def generate_private_key(k, n, m, order="deglex"):
    """
    Generates m oil-vinegar polynomials, where the first three are constructed
    as Q1, Q2, Q3 following the structure given. Additional random polynomials
    are generated and a random invertible matrix is applied to all of them.
    """
    # Polynomial ring for variables x1, ..., xn
    R = PolynomialRing(k, ["x%d" % i for i in range(1, n+1)], order=order)
    x = R.gens()

    # Vinegar and oil variables
    vinegar_vars = x[:n-m]
    oil_vars = x[n-m:]

    # Generate L1, L2, L3, L4
    L1 = sum(k.random_element() * xi for xi in vinegar_vars)
    L2 = sum(k.random_element() * xi for xi in x)
    L3 = sum(k.random_element() * xi for xi in vinegar_vars)
    L4 = sum(k.random_element() * xi for xi in vinegar_vars)

    # Construct Q1, Q2, Q3 as specified
    Q1 = L1^2 - L2 * L3
    Q2 = L1 * L3 - L2 * L4
    Q3 = L3^2 - L1 * L4

    # Add Q4, ..., Qm random oil-vinegar quadratics
    F = [Q1, Q2, Q3]
    for _ in range(m - 3):
        random_quad = sum(k.random_element() * xi * xj for xi in vinegar_vars for xj in x)
        F.append(random_quad)

    # Apply a random linear transformation using an invertible matrix A
    M = MatrixSpace(k, m, m)
    A = M.random_element()
    while not A.is_invertible():
        A = M.random_element()

    # Transform the polynomials using A
    F_transformed = [sum(A[i, j] * F[j] for j in range(m)) for i in range(m)]

    return F_transformed


def private_to_public_key(F, k, n, m):
    M = MatrixSpace(k, n)
    # Generate the secret transformation T.
    T = M.random_element()
    while not T.is_invertible():
        T = M.random_element()
    # Compose the central maps with T.
    P = [T.act_on_polynomial(f) for f in F]
    return P, T


def generate_keys(k, n, m, order="deglex"):
    F = generate_private_key(k, n, m)
    P,T = private_to_public_key(F, k, n, m)
    return P, F, T


def time_key_gen(q,n,m):
    k=GF(q)

    start_time = time.time()
    F = [0] * m
    retries=-1
    while any(poly == 0 for poly in F):
        F = generate_private_key(k, n, m)
        retries+=1
    #print("retries")
    #print(retries)
    P, T = private_to_public_key(F, k, n, m)
    end_time = time.time()

    time_taken = end_time - start_time

    return P, T, F, time_taken


def time_q_range_key_gen(q_range, n, m):
    time_dict = {}

    pp = prime_powers(q_range)

    all_verify_private_syzygy=True
    all_is_central_map=True
    all_verify_public_syzygy=True

    for q in pp:
        P, T, F, time_taken = time_key_gen(q,n,m)
        time_dict[(q, m, n)] = time_taken
        print(f"Time taken for q={q}, m={m}, n={n}: {time_taken} seconds")

        if not is_central_map(F, m):
            Q = [poly_to_matrix(f) for f in F]
            print(Q)
            print("Not Central!")
            all_is_central_map=False

    if all_is_central_map:
        print("All private keys are central maps!")
    else:
        print("NOT private all keys are central maps!")

    return time_dict


def time_n_range_key_gen(q, n_range, m):
    time_dict = {}

    all_verify_private_syzygy=True
    all_is_central_map=True
    all_verify_public_syzygy=True

    for n in range(m+1, n_range+1):
        P, T, F, time_taken = time_key_gen(q,n,m)
        time_dict[(q, m, n)] = time_taken
        print(f"Time taken for q={q}, m={m}, n={n}: {time_taken} seconds")

        if not is_central_map(F, m):
            Q = [poly_to_matrix(f) for f in F]
            print(Q)
            print("Not Central!")
            all_is_central_map=False

    if all_is_central_map:
        print("All private keys are central maps!")
    else:
        print("NOT private all keys are central maps!")

    return time_dict



def time_m_range_key_gen(q, n, m_range):
    time_dict = {}

    all_verify_private_syzygy=True
    all_is_central_map=True
    all_verify_public_syzygy=True

    for m in range(3, m_range+1):
        P, T, F, time_taken = time_key_gen(q,n,m)
        time_dict[(q, m, n)] = time_taken
        print(f"Time taken for q={q}, m={m}, n={n}: {time_taken} seconds")

        if not is_central_map(F, m):
            Q = [poly_to_matrix(f) for f in F]
            print(Q)
            print("Not Central!")
            all_is_central_map=False

    if all_is_central_map:
        print("All private keys are central maps!")
    else:
        print("NOT private all keys are central maps!")

    return time_dict




def prime_powers(limit):
    # Iterate through primes up to the square root of the limit (since p^2 should be <= limit)
    for p in primes(limit):
        power = 1
        while p^power <= limit:
            yield p^power
            power += 1


def time_multiple_ranges_key_gen(q_range, n_range, m_range):
    time_dict = {}

    pp = prime_powers(q_range)

    all_verify_private_syzygy=True
    all_is_central_map=True
    all_verify_public_syzygy=True

    for q in pp:
        for m in range(3, m_range+1):
            for n in range(m+1, n_range+1):
                P, T, F, time_taken = time_key_gen(q,n,m)
                time_dict[(q, m, n)] = time_taken
                print(f"Time taken for q={q}, m={m}, n={n}: {time_taken} seconds")

                if not is_central_map(F, m):
                    Q = [poly_to_matrix(f) for f in F]
                    print(Q)
                    print("Not Central!")
                    all_is_central_map=False

    if all_is_central_map:
        print("All private keys are central maps!")
    else:
        print("NOT private all keys are central maps!")

    return time_dict


def test_syzygy_gen(q_range, n_range, m_range):
    time_dict = {}

    pp = prime_powers(q_range)

    all_verify_private_syzygy=True
    all_is_central_map=True
    all_verify_public_syzygy=True

    for q in pp:
        for m in range(3, m_range+1):
            for n in range(m+1, n_range+1):
                print(q, n, m) 
                k=GF(q)
                R = PolynomialRing(k, ["x%d" % i for i in range(1, n + 1)], order="deglex")

                P, T, F, time_taken = time_key_gen(q,n,m)
                L = find_linear_syzygy(F, k, n, m)
                print(L)

                if not is_central_map(F, m):
                    all_is_central_map=False

                if L is None or not verify_syzygy(symbolic_to_polynomial2(L,R,k), F):
                    all_verify_private_syzygy=False

                if L is None or not verify_syzygy(apply_transformation(T, symbolic_to_polynomial2(L,R,k), R), P):
                    all_verify_public_syzygy=False

    if all_is_central_map:
        print("All private keys are central maps!")
    else:
        print("NOT private all keys are central maps!") 

    if all_verify_private_syzygy:
        print("All private keys contain a syzygy!")
    else:
        print("NOT all private keys contain a syzygy!")

    if all_verify_public_syzygy:
        print("All public keys contain a syzygy!")
    else:
        print("NOT all public keys contain a syzygy!")

    return 



###Run Tests
#time_dict = time_q_range_key_gen(200, 10, 4)
#time_dict = time_n_range_key_gen(16, 120, 60)
#time_dict = time_m_range_key_gen(16, 120, 60)
#time_dict = time_multiple_ranges_key_gen(50, 70, 60)
test_syzygy_gen(3, 10, 7)

