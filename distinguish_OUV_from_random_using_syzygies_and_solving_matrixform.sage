from sage.all import *

def generate_keys(k, n, m, order="deglex"):
    R = PolynomialRing(k, ["x%d" % i for i in range(1,n+1)], order=order)
    M = MatrixSpace(k, n)
    # Generate central maps.
    F = []
    for i in range(m):
        x = R.gens()
        f = 0
        for i in range(n-m):
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

def generate_poly(k, n, m, order="deglex"):
    """
    Generates public and private UOV keys, allowing oil-oil interactions in the private key polynomials.
    
    Args:
    - k: The finite field or ring.
    - n: The total number of variables (oil + vinegar).
    - m: The number of oil variables (m < n).
    - order: The monomial ordering for the polynomial ring (default is "deglex").
    
    Returns:
    - P: The public key polynomials (after applying the secret transformation).
    - F: The private key polynomials (with oil-oil interactions allowed).
    - T: The secret invertible linear transformation.
    """
    R = PolynomialRing(k, ["x%d" % i for i in range(1, n + 1)], order=order)
    M = MatrixSpace(k, n)
    
    # Generate central maps (private key polynomials F).
    F = []
    x = R.gens()
    for _ in range(m):
        f = 0
        # Loop over all pairs of variables (including oil-oil)
        for i in range(n):
            for j in range(i, n):
                f += k.random_element() * x[i] * x[j]  # Allow oil-oil, vinegar-oil, and vinegar-vinegar terms
        F.append(f)
    
    # Generate the secret transformation T (invertible matrix).
    T = M.random_element()
    while not T.is_invertible():
        T = M.random_element()
    
    # Compose the central maps with T to generate the public key polynomials P.
    P = [T.act_on_polynomial(f) for f in F]
    
    return P, F, T



def poly_to_matrix(f, symmetric=True):
    assert f.is_homogeneous() and f.degree() == 2, "f is not homogeneous"
    R = f.parent()
    k = R.base_ring()
    n = len(R.gens())
    
    # Initialize an empty matrix using MatrixSpace
    M = MatrixSpace(k, n, n)
    rows = []
    
    for i in range(n):
        row = [0] * n
        for j in range(i, n):
            m = R.gen(i) * R.gen(j)
            c = f.monomial_coefficient(m)
            row[j] = c
        rows.append(row)
    
    # Use MatrixSpace to construct the matrix explicitly
    Q = M(rows)
    
    if symmetric and k.characteristic() != 2:
        Q = (Q + Q.transpose()) / 2
    # For fields with characteristic 2, no symmetrization is performed
    return Q


def generate_public_key(amount, k, n, m, order="deglex"):
    P_polys = []
    P_matrices = []
    for i in range(amount):
        P, F, T = generate_keys(k, n, m, order=order)
        #print(F)
        #print(P)
        P_polys.append(P)
    return P_polys

def generate_random_key(amount, k, n, m, order="deglex"):
    P_polys = []
    P_matrices = []
    for i in range(amount):
        P, F, T = generate_poly(k, n, m, order=order)
        #print(F)
        #print(P)
        P_polys.append(P)
    return P_polys



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

    #print("Number of eq/var")
    #print(num_equations)
    #print(num_variables)

    # Print the theoretical number of equations/variables
    #print("Theoretical number of eq/var")
    #print(((n+2)*(n+1)*n/6)-((m+2)*(m+1)*m/6))
    #print(m*n)

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
        #print('eq')
        #print(eq)
        
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


def solution_to_linear_polynomials(solution, x, m, n, k):
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
    R = PolynomialRing(k, ["x%d" % i for i in range(1, n+1)])

    # Initialize an empty list to store the linear polynomials
    linear_polynomials = []

    # Iterate over each linear polynomial L_i
    for i in range(m):
        linear_poly = 0  # Start with a zero polynomial for L_i

        # Iterate over each x_j variable and the corresponding coefficient a_i_j
        for j in range(n):
            # Extract the coefficient a_i_j from the solution
            linear_poly += solution[i*n+j] * x[j]
            linear_poly = linear_poly.change_ring(R)
        # Add the constructed linear polynomial to the list
        linear_polynomials.append(linear_poly)

    return linear_polynomials




##################################################################################################
###Quadratic Syzygies
##################################################################################################
def find_kernel_quadratic_syzygy(F, k, n, m):
    """
    Check if there exists a syzygy among the polynomials in F, i.e.,
    if there are quadratic polynomials L1, ..., Lm such that:
    L1 * F1 + L2 * F2 + ... + Lm * Fm = 0.

    Also constructs a system of quadratic equations by summing up the symbolic coefficients
    for terms with the same monomial in x1, x2, ..., xn and equating them to zero.

    Returns the list of L1, ..., Lm if a syzygy is found, otherwise returns None.
    """
    # Step 1: Define the polynomial ring for variables x1, ..., xn and a_ij
    R = PolynomialRing(k, ["x%d" % i for i in range(1, n+1)] + [f'a_{l}_{i}_{j}' for l in range(m) for i in range(n) for j in range(i, n)])
    x = R.gens()[:n]  # Get the x variables (x1, ..., xn)
    a = R.gens()[n:]  # Get the a_ij variables

    x_vars = var(["x%d" % i for i in range(1, n+1)])  # Define the variables for x1, x2, ..., xn
    a_vars = var([f'a_{l}_{i}_{j}' for l in range(m) for i in range(n) for j in range(i, n)])

    # Step 2: Create m quadratic polynomials L1, ..., Lm, each with unknown coefficients a_ij
    L = []
    L_coeffs = []
    for l in range(m):
        L_i = sum(R(f'a_{l}_{i}_{j}') * x[i] * x[j] for i in range(n) for j in range(i, n))  # Create Li = a_i0*x1 + a_i1*x2 + ...
        L.append(L_i)

    # Step 3: Set up the syzygy equation: L1 * F1 + L2 * F2 + ... + Lm * Fm = 0
    syzygy_eq = sum(L[i] * F[i] for i in range(m))
    # print("syzygy_eq")
    # print(str(syzygy_eq))

    # Step 4: Expand and collect monomials to form a system of quadratic equations
    def construct_linear_system_from_syzygy(eq, n, m):
        """
        Given a polynomial equation, construct a system of linear equations by summing up
        the symbolic coefficients for terms with the same monomial in x1, x2, ..., xn
        and equating them to zero.
        """
        R = PolynomialRing(k, ["x%d" % i for i in range(1, n+1)]) # Include a_ij variables
        x = R.gens()

        x_vars = var(["x%d" % i for i in range(1, n+1)])  # Define the variables for x1, x2, ..., xn
        a_vars = var([f'a_{l}_{i}_{j}' for l in range(m) for i in range(n) for j in range(i, n)])


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

    R = PolynomialRing(k, ["x%d" % i for i in range(1, n+1)] + [f'a_{l}_{i}_{j}' for l in range(m) for i in range(n) for j in range(i, n)])

    # print("linear_system")
    # print(linear_system)

    # Step 6: Solve the system of equations for the unknown coefficients a_ij

    q=k.order()
    M, b = linear_system_to_matrix(linear_system, a_vars, q)

    #print('M')
    #print(M)

    kernel = M.right_kernel()
    #print(kernel)


    return kernel



def count_keys_with_quadratic_syzygies(P_polys, k, n, m):
    """
    Count how many of the public keys P contain a quadratic syzygy.
    
    Args:
    - P_polys: List of public keys, each being a list of polynomials.
    - k: Finite field (the base field).
    - n: Number of variables in the polynomials.
    - m: Number of polynomials in the system.
    
    Returns:
    - count: Number of keys that contain a quadratic syzygy.
    """
    count = 0
    
    # Loop over each public key P in P_polys
    for P in P_polys:
        kernel = find_kernel_quadratic_syzygy(P, k, n, m)  # Find the linear syzygy for the current key
        if kernel.basis() !=[]:  # If a linear syzygy is found, increase the count
            count += 1            
    return count





def test_number_of_quadratic_syzygies(amount, k, n, m, order="deglex"):
    print(test_number_of_quadratic_syzygies)

    P_polys = generate_public_key(amount, k, n, m, order="deglex") 
    syzygy_count_key = count_keys_with_quadratic_syzygies(P_polys, k, n, m)
    syzygy_prob_key = syzygy_count_key/amount
      
    P_polys_random = generate_random_key(amount, k, n, m, order="deglex")
    syzygy_count_random = count_keys_with_quadratic_syzygies(P_polys_random, k, n, m)
    syzygy_prob_random = syzygy_count_random/amount

    return syzygy_count_key, syzygy_prob_key, syzygy_count_random, syzygy_prob_random




##################################################################################################
###Lineair Syzygies
##################################################################################################
def find_kernel_linear_syzygy(F, k, n, m):
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

    q=k.order()
    M, b = linear_system_to_matrix(linear_system, a_vars, q)

    #print('M')
    #print(M)

    kernel = M.right_kernel()
    ##print(kernel)


    return kernel



def count_keys_with_linear_syzygies(P_polys, k, n, m):
    """
    Count how many of the public keys P contain a linear syzygy.
    
    Args:
    - P_polys: List of public keys, each being a list of polynomials.
    - k: Finite field (the base field).
    - n: Number of variables in the polynomials.
    - m: Number of polynomials in the system.
    
    Returns:
    - count: Number of keys that contain a linear syzygy.
    """
    count = 0
    
    # Loop over each public key P in P_polys
    for P in P_polys:
        kernel = find_kernel_linear_syzygy(P, k, n, m)  # Find the linear syzygy for the current key
        if kernel.basis() !=[]:  # If a linear syzygy is found, increase the count
            count += 1            
    return count

    


def test_number_of_lineair_syzygies(amount, k, n, m, order="deglex"):
    print(test_number_of_lineair_syzygies)

    P_polys = generate_public_key(amount, k, n, m, order="deglex") 
    syzygy_count_key = count_keys_with_linear_syzygies(P_polys, k, n, m)
    syzygy_prob_key = syzygy_count_key/amount
      
    P_polys_random = generate_random_key(amount, k, n, m, order="deglex")
    syzygy_count_random = count_keys_with_linear_syzygies(P_polys_random, k, n, m)
    syzygy_prob_random = syzygy_count_random/amount

    return syzygy_count_key, syzygy_prob_key, syzygy_count_random, syzygy_prob_random








##################################################################################################
###Lineair Dependencies
##################################################################################################


def find_linear_dependency(F, k, n, m):
    """
    Check if there exists a linear dependency among the polynomials in F, i.e.,
    if there are scalars c1, c2, ..., cm such that:
    c1 * F1 + c2 * F2 + ... + cm * Fm = 0, where not all c1, c2, ..., cm are zero.

    Returns the list of c1, ..., cm if a dependency is found, otherwise returns None.
    """
    # Step 1: Define the polynomial ring for variables x1, ..., xn and scalars c1, ..., cm
    R = PolynomialRing(k, ["x%d" % i for i in range(1, n+1)] + [f'c_{i}' for i in range(m)])
    x = R.gens()[:n]  # Get the x variables (x1, ..., xn)
    c = R.gens()[n:]  # Get the scalar variables (c1, ..., cm)

    x_vars = var(["x%d" % i for i in range(1, n+1)])  # Define the variables for x1, x2, ..., xn
    c_vars = var([f'c_{i}' for i in range(m)])  # Scalar variables for c1, ..., cm

    # Step 2: Set up the linear dependency equation: c1 * F1 + c2 * F2 + ... + cm * Fm = 0
    dependency_eq = sum(c[i] * F[i] for i in range(m))

    # Step 3: Expand and collect monomials to form a system of linear equations
    def construct_linear_system_from_dependency(eq, n, m):
        """
        Given a polynomial equation, construct a system of linear equations by summing up
        the symbolic coefficients for terms with the same monomial in x1, x2, ..., xn
        and equating them to zero.
        """
        # Expand the equation to combine like terms
        polynomial = SR(str(eq)).expand()

        # Extract terms and group them by monomials in x's
        monomial_dict = {}

        # Iterate through the terms of the expanded polynomial
        for term in polynomial.operands():
            coeff = term.subs({x: 1 for x in x_vars})  # Calculate the coefficient by setting all x variables to 1
            monomial_part = term / coeff
            monomial_part = monomial_part.expand()

            # Add the coefficient to the corresponding monomial (summing them up if monomial repeats)
            if monomial_part not in monomial_dict:
                monomial_dict[monomial_part] = coeff
            else:
                monomial_dict[monomial_part] += coeff

        # Construct the system of linear equations by equating the coefficients to zero
        linear_system = [coeff == 0 for monomial, coeff in monomial_dict.items()]
        return linear_system

    # Step 4: Construct the linear system from the dependency equation
    linear_system = construct_linear_system_from_dependency(dependency_eq, n, m)

    R = PolynomialRing(k, ["x%d" % i for i in range(1, n+1)] + [f'a_{i}_{j}' for i in range(m) for j in range(n)])

    # print("linear_system")
    # print(linear_system)

    # Step 6: Solve the system of equations for the unknown coefficients a_ij

    q=k.order()
    M, b = linear_system_to_matrix(linear_system, c_vars, q)

    #print('M')
    #print(M)

    kernel = M.right_kernel()
    #print(kernel)


    return kernel


def verify_dependency(L, F, x_vars):
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
    dependency_sum = sum(L[i] * F[i] for i in range(len(L)))

    # Simplify the result
    # syzygy_sum = syzygy_sum.simplify_full()

    if dependency_sum == 0:
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



def verify_dependency_symbolically(L, F, x_vars):
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
    dependency_sum = sum(SR(str(L[i])) * SR(str(F[i])) for i in range(len(L)))

    # Simplify the result
    dependency_sum = dependency_sum.simplify_full()

    if dependency_sum == 0:
        return True
    else:
        return False


def generate_keys_with_dependency(k, n, m, order="deglex"):
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
        L = find_linear_dependency(P, k, n, m)

        counter += 1

        if L != None:
            # If a syzygy is found, return the linear polynomials L1, ..., Lm
            return L, P, F, T

def test_find_linear_dependency():
    print(test_find_linear_dependency)
    works=True
    for _ in range(10):
        k = GF(2)  # Finite field (can be modified)
        n = 5  # Number of variables
        m = 3  # Number of polynomials
        x_vars = var(["x%d" % i for i in range(1, n+1)])
        R = PolynomialRing(k, ["x%d" % i for i in range(1, n + 1)], order="deglex")

        L, P, F, T = generate_keys_with_dependency(k, n, m)
        L_poly=symbolic_to_polynomial(L,R)

        if not verify_dependency(L_poly, F, x_vars) or not verify_dependency(L_poly, P, x_vars):
            works=False

    if works:
        return "test_find_linear_dependency works"
    else:
        return "test_find_linear_dependency does NOT work"
#print(test_find_linear_dependency())


def count_keys_with_linear_dependencies(P_polys, k, n, m):
    """
    Count how many of the public keys P contain a linear syzygy.
    
    Args:
    - P_polys: List of public keys, each being a list of polynomials.
    - k: Finite field (the base field).
    - n: Number of variables in the polynomials.
    - m: Number of polynomials in the system.
    
    Returns:
    - count: Number of keys that contain a linear syzygy.
    """
    count = 0
    
    # Loop over each public key P in P_polys
    for P in P_polys:
        kernel = find_linear_dependency(P, k, n, m)  # Find the linear syzygy for the current key
        if kernel.basis() != []:  # If a linear syzygy is found, increase the count
            count += 1
            
    return count


    


def test_number_of_lineair_dependencies(amount, k, n, m, order="deglex"):
    print(test_number_of_lineair_dependencies)

    P_polys = generate_public_key(amount, k, n, m, order="deglex") 
    dependency_count_key = count_keys_with_linear_dependencies(P_polys, k, n, m)
    dependency_prob_key = dependency_count_key/amount
      
    P_polys_random = generate_random_key(amount, k, n, m, order="deglex")
    dependency_count_random = count_keys_with_linear_dependencies(P_polys_random, k, n, m)
    dependency_prob_random = dependency_count_random/amount

    return dependency_count_key, dependency_prob_key, dependency_count_random, dependency_prob_random


q=2
k=GF(q)
n=6
m=4
runs=100000

dependency_count_key, dependency_prob_key, dependency_count_random, dependency_prob_random = test_number_of_lineair_dependencies(runs, k, n, m, order="deglex")

runs=1
syzygy_count_key, syzygy_prob_key, syzygy_count_random, syzygy_prob_random = test_number_of_lineair_syzygies(runs, k, n, m, order="deglex")

quadratic_syzygy_count_key, quadratic_syzygy_prob_key, quadratic_syzygy_count_random, quadratic_syzygy_prob_random = test_number_of_quadratic_syzygies(runs, k, n, m, order="deglex")




print("UOV")
print(dependency_count_key)
print("Empirical Prob.")
print(dependency_prob_key)
print("Theoretical Prob.")
print(k.order()**(m - n*(n+1)/2 + m*(m+1)/2))

print("\n")

print("Random")
print(dependency_count_random)
print("Empirical Prob.")
print(dependency_prob_random)
print("Theoretical Prob.")
print(k.order()**(m - n*(n+1)/2))

print("\n")

print("Compare Empirical (UOV/Random)")
#print(dependency_prob_key/dependency_prob_random)    
print("Compare Theoretical (UOV/Random)")
#print((k.order()**(n**2-n**3+m**3))/(k.order()**(n**2-n**3)))


print("UOV")
print(syzygy_count_key)
print("Empirical Prob.")
print(syzygy_prob_key)
print("Theoretical Prob.")
print(k.order()**(n**2-n**3+m**3))
print("Theoretical Prob. 2")
print(k.order()**(-n))

print("\n")

print("Random")
print(syzygy_count_random)
print("Empirical Prob.")
print(syzygy_prob_random)
print("Theoretical Prob.")
print(k.order()**(n**2-n**3))
print("Theoretical Prob. 2")
print(k.order()**(-n))

print("\n")

print("Compare Empirical (UOV/Random)")
#print(syzygy_prob_key/syzygy_prob_random)    
print("Compare Theoretical (UOV/Random)")
#print((k.order()**(n**2-n**3+m**3))/(k.order()**(n**2-n**3)))


print("UOV")
print(quadratic_syzygy_count_key)
print("Empirical Prob.")
print(quadratic_syzygy_prob_key)
print("Theoretical Prob.")
print(k.order()**(n**2-n**3+m**3))
print("Theoretical Prob. 2")
print(k.order()**(-n))

print("\n")

print("Random")
print(quadratic_syzygy_count_random)
print("Empirical Prob.")
print(quadratic_syzygy_prob_random)
print("Theoretical Prob.")
print(k.order()**(n**2-n**3))
print("Theoretical Prob. 2")
print(k.order()**(-n))

print("\n")

print("Compare Empirical (UOV/Random)")
#print(syzygy_prob_key/syzygy_prob_random)    
print("Compare Theoretical (UOV/Random)")
#print((k.order()**(n**2-n**3+m**3))/(k.order()**(n**2-n**3)))


def multiple_dependency_tests():
    q=2
    k=GF(q)
    n=4
    m=3
    runs=10000

    dependency_count_key_list=[]
    dependency_prob_key_list=[]
    dependency_count_random_list=[]
    dependency_prob_random_list=[]
    for _ in range(11):
        dependency_count_key, dependency_prob_key, dependency_count_random, dependency_prob_random = test_number_of_lineair_dependencies(runs, k, n, m, order="deglex")
        
        dependency_count_key_list.append(dependency_count_key)    
        dependency_prob_key_list.append(dependency_prob_key)    
        dependency_count_random_list.append(dependency_count_random)    
        dependency_prob_random_list.append(dependency_prob_random)

    print(dependency_count_key_list)
    print(dependency_prob_key_list)
    print(dependency_count_random_list)
    print(dependency_prob_random_list)

#multiple_dependency_tests()


def multiple_syzygy_tests():
    q=2
    k=GF(q)
    n=6
    m=5
    runs=10000

    syzygy_count_key_list=[]
    syzygy_prob_key_list=[]
    syzygy_count_random_list=[]
    syzygy_prob_random_list=[]
    for _ in range(11):
        syzygy_count_key, syzygy_prob_key, syzygy_count_random, syzygy_prob_random = test_number_of_lineair_syzygies(runs, k, n, m, order="deglex")
        
        syzygy_count_key_list.append(syzygy_count_key)    
        syzygy_prob_key_list.append(syzygy_prob_key)    
        syzygy_count_random_list.append(syzygy_count_random)    
        syzygy_prob_random_list.append(syzygy_prob_random)

    print(syzygy_count_key_list)
    print(syzygy_prob_key_list)
    print(syzygy_count_random_list)
    print(syzygy_prob_random_list)

#multiple_syzygy_tests()



