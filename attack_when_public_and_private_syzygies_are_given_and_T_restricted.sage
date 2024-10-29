import random


# is_central_map returns true if all elements of the specified list of
# matrices Q have zero submatrix corresponding to the oil variables.
def is_central_map(Q, m):
    for M in Q:
        n, _ = M.dimensions()
        if not M.submatrix(n-m, n-m).is_zero():
            return False
    return True
    
    
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
    
def linear_system_to_matrix(equations, variables, q):
    """
    Transforms a system of linear equations into its corresponding matrix form
    and also extracts the constant terms vector.

    :param equations: List of linear equations.
    :param variables: List of variables to solve for.
    :param q: Field size (used to define the finite field GF(q)).
    :return: Coefficient matrix A and constant terms vector b.
    """
    # Number of equations and variables
    num_equations = len(equations)
    num_variables = len(variables)

    print("Number of eq/var")
    print(num_equations)
    print(num_variables)

    # Print the theoretical number of equations/variables
    print("Theoretical number of eq/var")
    print(((n+2)*(n+1)*n/6)-((m+2)*(m+1)*m/6))
    print(m*n)

    # Define the finite field GF(q)
    k = GF(q)
    k.inject_variables()

    # Initialize an empty matrix to store coefficients
    A = matrix(k, num_equations, num_variables)  # Coefficient matrix

    # Initialize an empty vector to store the constant terms (right-hand side)
    b = vector(k, num_equations)

    # Loop through each equation to extract coefficients and constants
    for i, eq in enumerate(equations):
        # Move all terms to the left-hand side: f(x) = b => f(x) - b = 0
        eq = eq.lhs() - eq.rhs()
        print('eq')
        print(eq)
        
        # Extract coefficients for each variable
        for j, var in enumerate(variables):
            A[i, j] = eq.coefficient(var)

        # Extract the constant term by subtracting the variable terms from the equation
        constant = eq
        for var in variables:
            constant -= eq.coefficient(var) * var

        # Set the constant term in the right-hand side vector
        b[i] = -constant  # Move the constant to the right-hand side (so, multiply by -1)
    
    return A, b



def find_possible_T(L, L_prime, n, m, q):
    """
    Given two lists of linear polynomials L = [L_1, ..., L_m] and L' = [L'_1, ..., L'_m],
    find all possible linear transformations T such that L'_i(x) = L_i(T(x)) for all i.

    Args:
        L (list): List of m linear polynomials L_i in n variables over GF(q).
        L_prime (list): List of m linear polynomials L'_i in n variables over GF(q).
        n (int): The number of variables (dimension of the transformation).
        q (int): The size of the finite field GF(q).

    Returns:
        list: List of possible linear transformation matrices T that satisfy the relation.
    """
    # Define symbolic variables x_1, x_2, ..., x_n (as symbolic expressions in SR)
    x_vars = var(['x%d' % i for i in range(1, n+1)])
    x_vec = vector(SR, x_vars)  # Symbolic vector x

    # Compute v = n - m, the size of the upper identity matrix
    v = n - m

    # Create the block structure for T
    I_v = identity_matrix(SR, v)  # Identity matrix of size v x v
    I_m = identity_matrix(SR, m)  # Identity matrix of size m x m
    zero_block = Matrix(SR, m, v)  # Zero matrix of size m x v
    T_prime_vars = Matrix(SR, v, m, var('T_prime_' + ',T_prime_'.join([f'{i}{j}' for i in range(1, v+1) for j in range(1, m+1)])))
    print('T_prime_vars.liest()')
    print(T_prime_vars.list())

    # Construct the full transformation matrix T in block form
    T_vars = block_matrix([[I_v, T_prime_vars], [zero_block, I_m]])
    print('T_vars')
    print(T_vars)

    # Define the transformed variables T(x) = T * x
    Tx = T_vars * x_vec
    print('Tx')
    print(Tx)    

    print('L')
    print(L)
    print('L_prime')
    print(L_prime)

    # Create symbolic versions of the polynomials in L and L_prime
    L_symbolic = [SR(str(L_i)) for L_i in L]  # Convert to SR using string conversion
    L_prime_symbolic = [SR(str(L_prime_i)) for L_prime_i in L_prime]

    print('L_symbolic')
    print(L_symbolic)
    print('L_prime_symbolic')
    print(L_prime_symbolic)

    # Create the system of equations L'_i(x) = L_i(T(x)) for all i
    equations = []
    for i in range(len(L)):
        # Substitute T(x) into L_i (all symbolic now)
        L_i_Tx = L_symbolic[i].subs({x_vars[j]: Tx[j] for j in range(n)})
        # Set up the equation L'_i(x) = L_i(T(x))
        equations.append(L_prime_symbolic[i] == L_i_Tx)

    print('equations')
    print(equations)

    print('T_prime_vars.list')
    print(T_prime_vars.list())

    def symbolic_to_linear_system(equations, x_vars, T_vars):
        """
        Transforms a list of symbolic equations into a linear system by assuming
        that each equation holds for all values of x_vars. The result is a set of
        linear equations in T_vars.

        Args:
        - equations: List of symbolic equations (e.g., x1 + x2 == T11*x1 + T12*x2).
        - x_vars: List of symbolic variables (e.g., [x1, x2, ..., xn]).
        - T_vars: Dictionary of symbolic T variables, with keys being (i, j) indices
                  and values being the corresponding Sage symbolic variables (e.g., {(1, 1): T11}).

        Returns:
        - A list of linear equations in the T_vars.
        """
        linear_system = []

        # Loop over each equation in the system
        for eq in equations:
            # Expand the equation to separate terms
            lhs, rhs = eq.lhs().expand(), eq.rhs().expand()

            # Subtract rhs from lhs so that we equate the entire expression to 0
            combined_expr = lhs - rhs

            # Collect coefficients of each variable in x_vars
            for x in x_vars:
                # Get the coefficient of the current variable x
                coeff_x = combined_expr.coefficient(x)

                # Set this coefficient to 0 to form a linear equation in T_vars
                linear_system.append(coeff_x == 0)

        return linear_system

    def detect_nonsensical_equations(linear_system):
        """
        Filters out nonsensical equations from the linear system.
        Nonsensical equations are those where there is no variable and the equation
        itself is inconsistent (e.g., -1 == 0, 4 == 0), but keeps valid equations like 0 == 0.

        Args:
            linear_system (list): A list of linear equations (e.g., [-1 == 0, 4 == 0, T_11 - T_12 == 0]).

        Returns:
            list: A filtered list of valid equations.
        """
        nonsense = False
        
        for eq in linear_system:
            # Check if both sides of the equation are constants
            lhs, rhs = eq.lhs(), eq.rhs()
            
            # If lhs is a constant and rhs is a constant, check if they are equal
            if lhs.is_constant() and rhs.is_constant():
                if lhs != rhs:
                    # Keep equations like 0 == 0
                    nonsense = True

        return nonsense


    linear_system = symbolic_to_linear_system(equations, x_vars, T_prime_vars.list())
    print('linear_system')
    print(linear_system)

    if detect_nonsensical_equations(linear_system):
        return None, None

    M, b = linear_system_to_matrix(linear_system, T_prime_vars.list(), q)

    print('M')
    print(M)
    print('M_rank')
    print(M.rank())
    print('b')
    print(b)

    def vector_to_square_matrix(v, k):
        """
        Transforms a vector into a square matrix if the length of the vector is a perfect square.

        :param v: A vector (tuple, list, or Sage vector) of length n^2.
        :return: A square matrix of size n x n, or raise an error if the length of v is not a perfect square.
        """
        # Determine the length of the vector
        length = len(v)

        # Check if the length is a perfect square
        n = int(sqrt(length))
        if n * n != length:
            raise ValueError("The length of the vector is not a perfect square.")

        # Convert the vector into a square matrix
        matrix_v = matrix(k, n, n, v)  # You can change QQ to another ring, like GF(q)
        # print('matrix_v')
        # print(matrix_v)
        return matrix_v

    particular_soln = M.solve_right(b)
    print('particular_soln')
    print(particular_soln)

    kernel = M.right_kernel()
    print('kernel')
    print(kernel)


    solutions=[]
    particular_soln = M.solve_right(b)
    for homogeneous_soln in M.right_kernel():
        solution=particular_soln + homogeneous_soln
        solutions.append(solution)
    print('solutions')
    print(solutions)
    


    return solutions



    # Solve the system of equations for the unknowns in T_vars
    #sol = solve(equations, T_vars.list(), solution_dict=True)

    # Convert the solutions into matrices and return the result
    #possible_Ts = []
    #for solution in solutions:
     #   T_matrix = vector_to_square_matrix(solution, k)
      #  possible_Ts.append(T_matrix)

    #return possible_Ts



def generate_keys(k, n, m, order="deglex"):
    """
    Generates random linear polynomials L1, ..., Lm over a field k with n variables.
    """
    R = PolynomialRing(k, ["x%d" % i for i in range(1,n+1)], order=order)
    x = R.gens()

    # Generate m random linear polynomials L1, ..., Lm
    L = []
    for i in range(m):
        linear_poly = sum(k.random_element() * x[j] for j in range(n))
        L.append(linear_poly)
    
    return L

def find_linear_dependency(L, k, n, m):
    """
    Check if there exists a dependency among the polynomials in L, i.e.,
    if there are quadratic polynomials F1, ..., Fm such that:
    L1 * F1 + L2 * F2 + ... + Lm * Fm = 0.

    Constructs a system of linear equations by summing up the symbolic coefficients
    for terms with the same monomial in x1, x2, ..., xn and equating them to zero.

    Returns the list of F1, ..., Fm if a solution is found, otherwise returns None.
    """
    # Step 1: Define the polynomial ring for variables x1, ..., xn and f_ij
    R = PolynomialRing(k, ["x%d" % i for i in range(1, n+1)] + [f'f_{l}_{i}_{j}' for l in range(m) for i in range(n-m) for j in range(n)])
    x = R.gens()[:n]  # Get the x variables (x1, ..., xn)
    f_vars = R.gens()[n:]  # Get the f_ij variables

    x_vars = var(["x%d" % i for i in range(1, n+1)])  # Define the variables for x1, x2, ..., xn
    f_vars = var([f'f_{l}_{i}_{j}' for l in range(m) for i in range(n-m) for j in range(i,n)])

    # Step 2: Create m quadratic polynomials F1, ..., Fm, each with unknown coefficients f_ij
    F = []
    for l in range(m):
        f = 0
        for i in range(n - m):
            start_index = i
            for j in range(start_index, n):
                f += R(f'f_{l}_{i}_{j}') * x[i] * x[j]
        F.append(f)

    # Step 3: Set up the dependency equation: L1 * F1 + L2 * F2 + ... + Lm * Fm = 0
    dependency_eq = sum(L[i] * F[i] for i in range(m))

    # Step 4: Expand and collect monomials to form a system of linear equations
    def construct_linear_system_from_dependency(eq, n, m):
        """
        Given a polynomial equation, construct a system of linear equations by summing up
        the symbolic coefficients for terms with the same monomial in x1, x2, ..., xn
        and equating them to zero.
        """
        R = PolynomialRing(k, ["x%d" % i for i in range(1, n+1)]) # Include f_ij variables
        x = R.gens()

        x_vars = var(["x%d" % i for i in range(1, n+1)])  # Define the variables for x1, x2, ..., xn
        f_vars = var([f'f_{l}_{i}_{j}' for l in range(m) for i in range(n-m) for j in range(i,n)])


        # Step 2: Parse the equation string into a symbolic expression and simplify
        polynomial = SR(str(eq)).expand()  # Expand the equation to combine like terms

        # Step 3: Extract terms and group them by monomials in x's
        monomial_dict = {}

        # Iterate through the terms of the expanded polynomial
        for term in polynomial.operands():
            coeff = term.subs({x:1 for x in x_vars})  # Calculate the coefficient by setting all x variables to 1
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

    # Step 5: Construct the linear system from the dependency equation
    linear_system = construct_linear_system_from_dependency(dependency_eq, n, m)

    # Step 6: Solve the system of equations for the unknown coefficients f_ij
    solutions = solve(linear_system, f_vars)

    # Check if a solution exists and is non-trivial
    def is_non_trivial_solution(solution):
        """
        Checks if a solution to a system of equations is trivial (all variables are zero).
        """
        for equation in solution:
            if equation.rhs() != 0:  # Access the right-hand side of the equation to check the value
                return True
        return False

    for solution in solutions:
        if is_non_trivial_solution(solution):
            return solution_to_quadratic_polynomials(solution, x_vars, m, n)  # Return the solution for F
    return None  # No non-trivial solution found


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


def generate_keys_with_dependency(k, n, m, order="deglex"):
    """
    Continuously generate random linear polynomials L and check for linear dependencies in F.
    If a dependency is found, return the quadratic polynomials F1, ..., Fm.
    """
    counter = 0
    while True:
        # Generate random linear polynomials L
        L = generate_keys(k, n, m, order)

        # Check if a linear dependency exists in the generated polynomials
        F = find_linear_dependency(L, k, n, m)

        counter += 1
        # print(counter)



        if F is not None:
            # If a dependency is found, return the quadratic polynomials F1, ..., Fm
            return F, L

def solution_to_quadratic_polynomials(solution, x_vars, m, n):
    """
    Transform the solution coefficients into the corresponding quadratic polynomials.

    Args:
    solution (list): A list of equations representing the solution.
    x_vars (list): A list of variables (x1, x2, ..., xn) corresponding to the quadratic polynomials.
    m (int): The number of quadratic polynomials.
    n (int): The number of x variables.

    Returns:
    list: A list of quadratic polynomials corresponding to the solution.
    """
    quadratic_polynomials = []
    # Iterate over each quadratic polynomial F_i
    for l in range(m):
        quadratic_poly = 0
        for i in range(n - m):
            start_index = i

        # Iterate over each x_j variable and the corresponding coefficient f_i_j
            for j in range(start_index, n):
                coeff = None
                for eq in solution:
                    if eq.lhs() == var(f'f_{l}_{i}_{j}'):
                        coeff = eq.rhs()  # Get the right-hand side value (the coefficient)
                        break

                # Add the term coeff * x_j^2 to the quadratic polynomial
                if coeff != 0:
                    quadratic_poly += coeff * x_vars[i] * x_vars[j]

        quadratic_polynomials.append(quadratic_poly)

    return quadratic_polynomials


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

def private_to_public(F, k, n, m, order="deglex"):
    R = PolynomialRing(k, ["x%d" % i for i in range(1, n+1)], order=order)
    v = n - m
    I_v = identity_matrix(k, v)
    I_m = identity_matrix(k, m)
    zero_block = Matrix(k, m, v)  # Zero matrix of size m x v
    T_prime = Matrix(k, v, m, [k.random_element() for _ in range(v * m)])  # Random v x m matrix T'

    # Construct the full transformation matrix T in block form
    T = block_matrix([[I_v, T_prime], [zero_block, I_m]])

    # Compose the central maps with T
    print("F")
    print(F)
    print("T")
    print(T)

    P = [T.act_on_polynomial(f) for f in F]
    
    return P, T




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


    M, b = linear_system_to_matrix(linear_system, a_vars, q)
    matrix_rank = M.rank()

    solutions=[]
    particular_soln = M.solve_right(b)
    for homogeneous_soln in M.right_kernel():
        solution=particular_soln + homogeneous_soln
        if solution != vector(GF(q),[0]*len(a_vars)):
            solutions.append(solution)




    def solution_to_linear_polynomials(solution, x, m, n):
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
                linear_poly += solution[i*n+j] * x[j]

            # Add the constructed linear polynomial to the list
            linear_polynomials.append(linear_poly)

        return linear_polynomials


    solution_polys=[]
    for solution in solutions:
        solution_polys.append(solution_to_linear_polynomials(solution, x, m, n))

    return solution_polys


def apply_linear_transformation(polynomial, T_matrix, R):
    """
    Applies a linear transformation to a polynomial.

    :param polynomial: The polynomial to transform.
    :param T_matrix: The matrix representing the linear transformation.
    :param R: The polynomial ring containing the polynomial.
    :return: The transformed polynomial.
    """

    x_vars = R.gens()  # Get the variables (x1, x2, ..., xn) from the polynomial ring
    n = len(x_vars)    # Number of variables

    # Step 1: Compute the images of the x-variables under the transformation T
    transformed_vars = [sum(T_matrix[i, j] * x_vars[j] for j in range(n)) for i in range(n)]

    # Step 2: Substitute each x_i in the polynomial with T(x_i)
    transformed_poly = polynomial.subs({x_vars[i]: transformed_vars[i] for i in range(n)})

    return transformed_poly



q=103
k=GF(q)
n=5
m=2

x_vars = var(["x%d" % i for i in range(1, n+1)])
R = PolynomialRing(k, ["x%d" % i for i in range(1, n + 1)], order="deglex")

F_polys = [0] * m
while any(poly == 0 for poly in F_polys):
    F, L_private = generate_keys_with_dependency(k, n, m)
    F_polys = symbolic_to_polynomial2(F, R, k)    #ZeroDivisionError: inverse of Mod(0, 2) does not exist
    print('L_private')
    print(L_private)
    print('F_polys')
    print(F_polys)
P, T = private_to_public(F_polys, k, n, m)
print(P)
print('T')
print(T)

x_prime = [T.act_on_polynomial(xi) for xi in R.gens()]
print('x_prime')
print(x_prime)

print(T.rank())
print('Private syzygy vrfifies')
print(verify_syzygy(L_private,F_polys))

x=R.gens()
print('x')
print(x)

L_public1=[]
for L in L_private:
    L_public1.append(apply_linear_transformation(L, T, R))
print('L_public1')
print(L_public1)


L_public = find_linear_syzygy(P, k, n, m)
print('L_public')
print(L_public)
print('L_public syzygy vrfifies')
print(verify_syzygy(L_public[0],P))

print('L_public1 in L_public')
print(L_public1 in L_public)

x=R.gens()
print('x')
print(x)



def create_matrix_from_tuples(tuple_list, n, m):
    """
    Creates a list of n x n matrices based on the input tuple_list.
    Each tuple in tuple_list provides the elements of T_prime to be substituted in the matrix.
    
    Parameters:
        tuple_list: A list of tuples of size (n-m)*m
        n: Total size of the matrix (n x n)
        m: Size of the bottom-right block (m x m)
        
    Returns:
        A list of n x n matrices.
    """
    v = n - m  # Size of the top-left identity block
    
    # Initialize an empty list to store the matrices
    matrix_list = []
    
    # Create identity matrices and zero block
    I_v = identity_matrix(SR, v)  # Identity matrix of size v x v
    I_m = identity_matrix(SR, m)  # Identity matrix of size m x m
    zero_block = Matrix(SR, m, v)  # Zero matrix of size m x v

    # Create T_prime as symbolic variables matrix (v x m)
    T_prime_vars = Matrix(SR, v, m, var('T_prime_' + ',T_prime_'.join([f'{i}{j}' for i in range(1, v+1) for j in range(1, m+1)])))

    # Loop over each tuple to substitute values into the matrix
    for tpl in tuple_list:
        # Create the overall matrix
        top_matrix = I_v.augment(T_prime_vars)   # Concatenate I_v with T_prime_vars
        bottom_matrix = zero_block.augment(I_m)  # Concatenate zero block with I_m
        M = top_matrix.stack(bottom_matrix)      # Stack the two parts to form the full matrix
        
        # Substitute values from the tuple into the T_prime part
        substitution_dict = {T_prime_vars[i, j]: SR(tpl[i * m + j]) for i in range(v) for j in range(m)}
        M_substituted = M.substitute(substitution_dict)
        
        # Append the substituted matrix to the list
        matrix_list.append(M_substituted)
    
    return matrix_list


for L in L_public:
    solutions = find_possible_T(L_private, L, n, m, q)
    print('solutions1')
    print(solutions)
    solutions_matrix = create_matrix_from_tuples(solutions, n, m)
    print('solutions_matrix')
    print(solutions_matrix)










def reshape_vector_to_matrix(vec, n):
    """
    Reshape a vector of length n^2 into an n x n matrix.
    """
    return Matrix(GF(2), n, n, vec)

def greedy_rank_optimization_random(particular_soln, kernel_basis, n, max_attempts=10):
    """
    Optimizes the rank of the matrix representation of a solution, exploring
    the solution space more thoroughly by introducing randomness and backtracking.
    
    :param particular_soln: The particular solution vector of length n^2.
    :param kernel_basis: The basis vectors of the kernel as a list of vectors.
    :param n: The size of the matrix (n x n).
    :param max_attempts: The maximum number of backtracking attempts.
    :return: The optimized solution as a vector and its matrix representation.
    """
    best_solution = vector(GF(2), particular_soln)
    kernel_basis_copy = kernel_basis.copy()
    
    for attempt in range(max_attempts):
        # Shuffle the kernel basis for randomness
        random.shuffle(kernel_basis_copy)
        current_solution = best_solution  # Start with the particular solution
        x_matrix = reshape_vector_to_matrix(current_solution, n)
        max_rank = x_matrix.rank()
        
        for basis_vec in kernel_basis_copy:
            candidate_solution = current_solution + basis_vec
            candidate_matrix = reshape_vector_to_matrix(candidate_solution, n)
            candidate_rank = candidate_matrix.rank()
            
            # Introduce some random perturbation to escape local maxima
            if candidate_rank > max_rank or random.random() < 0.1:
                current_solution = candidate_solution
                max_rank = candidate_rank
                
            # If we reach full rank, stop early
            if max_rank == n:
                return current_solution, reshape_vector_to_matrix(current_solution, n)
        
        # Backtracking: keep trying with different randomizations if stuck
        if attempt % 2 == 0:
            print('Backtracking...')
            best_solution = vector(GF(2), [random.choice([0, 1]) for _ in range(len(particular_soln))])

    # Return the best solution found
    return current_solution, reshape_vector_to_matrix(current_solution, n)




for L in L_public:
    part_sol, kernel_matrix = find_possible_T(L_private, L, n, m, q)

    if part_sol is not None:

        F_is_central=False
        while not F_is_central:

            rank_best_solution=0
            while rank_best_solution!=n:
                best_solution, best_solution_matrix = greedy_rank_optimization_random(part_sol, kernel_matrix, n)
                rank_best_solution = best_solution_matrix.rank()
                #print(best_solution_matrix)

            possible_F=[]
            for p in P:
                possible_F.append(apply_linear_transformation(p,best_solution_matrix.inverse(),R))
            #print(possible_F)
            possible_F_matrix = [poly_to_matrix(f) for f in possible_F]
            #print(possible_F_matrix)
            if is_central_map(possible_F_matrix, m):
                F_is_central=True
        
        possible_L_private = find_linear_syzygy(possible_F, k, n, m)

        print(best_solution_matrix)
        print(possible_F)
        print(possible_L_private)

print('F_polys')
print(F_polys)

print('L_private')
print(L_private)

print('Private key that was found with attack contains original private syzygy:')
print(L_private in possible_L_private)




