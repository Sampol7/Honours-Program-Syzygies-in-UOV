from sage.all import *
import time

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
    f_vars = var([f'f_{l}_{i}_{j}' for l in range(m) for i in range(n-m) for j in range(n)])

    # Step 2: Create m quadratic polynomials F1, ..., Fm, each with unknown coefficients f_ij
    F = []
    for l in range(m):
        f = 0
        for i in range(n - m):
            start_index = i
            for j in range(start_index, n):
                f += R(f'f_{l}_{i}_{j}') * x[i] * x[j]
        F.append(f)

    #print('F')
    #print(F)
    # Step 3: Set up the dependency equation: L1 * F1 + L2 * F2 + ... + Lm * Fm = 0
    #print('L')
    #print(L)
    dependency_eq = sum(L[i] * F[i] for i in range(m))
    #print('dependency_eq')
    #print(dependency_eq)

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
        f_vars = var([f'f_{l}_{i}_{j}' for l in range(m) for i in range(n-m) for j in range(n)])


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
        #print('linear_system')
        #print(linear_system)
        return linear_system

    # Step 5: Construct the linear system from the dependency equation
    linear_system = construct_linear_system_from_dependency(dependency_eq, n, m)

    R = PolynomialRing(k, ["x%d" % i for i in range(1, n+1)] + [f'f_{l}_{i}_{j}' for l in range(m) for i in range(n-m) for j in range(n)])

    q=k.order()
    #print(f_vars)
    M, b = linear_system_to_matrix(linear_system, f_vars, q)
    #print('M, b')
    #print(M, b)
    matrix_rank = M.rank()

    solutions = []
    particular_soln = M.solve_right(b)
    #print(particular_soln)
    kernel = M.right_kernel()
    #print(kernel)

    zero=True
    F=[]
    # Genereer een willekeurige oplossing
    while zero:  # Probeer 10 keer (of pas dit aantal aan naar behoefte)
        random_coeffs = [randint(0, 1) for _ in range(kernel.dimension())]
        #print('random_coeffs')
        #print(random_coeffs)
        homogeneous_soln = sum(coeff * vector(GF(q), kernel.basis()[i]) for i, coeff in enumerate(random_coeffs))
        #print('homogeneous_soln')
        #print(homogeneous_soln)
        solution = particular_soln + homogeneous_soln
        #print('f_vars')
        #print(f_vars)
        #print('solution')
        #print(solution)
        F = solution_to_quadratic_polynomials(solution, x, m, n)
        #print('F')
        #print(F)
        if not any(poly == 0 for poly in F):
            zero=False

    return F

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
        # #print(counter)

        if F != []:
            # If a dependency is found, return the quadratic polynomials F1, ..., Fm
            return F, L

def solution_to_quadratic_polynomials(solution, x, m, n):
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
    #print('solution')
    #print(solution)

    # Initialize an empty list to store the quadratic polynomials
    quadratic_polynomials = []

    # Iterate over each quadratic polynomial L_i
    for l in range(m):
        quadratic_poly = 0  # Start with a zero polynomial for L_i

        # Iterate over each x_j variable and the corresponding coefficient a_i_j
        for i in range(n-m):
            for j in range(i,n):
                # Extract the coefficient a_i_j from the solution
                quadratic_poly += solution[l*((n-m)*n)+i*n+j] * x[i] * x[j]
        # Add the constructed quadratic polynomial to the list
        quadratic_polynomials.append(quadratic_poly)


    return quadratic_polynomials
    

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



def verify_syzygy_symbolically(L, F, x_vars, q, R):
    """
    Verify if L1 * F1 + L2 * F2 + ... + Lm * Fm = 0.

    Args:
    L (list): List of linear polynomials L1, ..., Lm.
    F (list): List of private key polynomials F1, ..., Fm.
    x_vars (list): List of variables (x1, x2, ..., xn).

    Returns:
    bool: True if L1 * F1 + L2 * F2 + ... + Lm * Fm = 0, False otherwise.
    """
    k=GF(q)

    # Ensure that the lengths of L and F are the same
    if len(L) != len(F):
        raise ValueError("Length of L and F must be the same")

    # Compute the sum L1 * F1 + L2 * F2 + ... + Lm * Fm
    syzygy_sum = sum(SR(str(L[i])) * SR(str(F[i])) for i in range(len(L)))
    #print(syzygy_sum)
    # Simplify the result
    syzygy_sum = syzygy_sum.simplify_full()
    #print(syzygy_sum)

    syzygy_sum = R(syzygy_sum)
    #print(syzygy_sum)

    if syzygy_sum == 0:
        return True
    else:
        return False

def symbolic_to_polynomial(symbolic_expressions, R, k):
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
                        random_replacements[var_str] = int(k.random_element())  # Assign random field element
                    substitutions[var] = random_replacements[var_str]
            
            # Substitute the 'r' variables with their corresponding random values
            substituted_expressions.append(expr.subs(substitutions))
        else:
            substituted_expressions.append(expr)

    #print(symbolic_expressions)    
    #print(random_replacements)    
    #print(substituted_expressions)    
    # Convert the substituted expressions into elements of the polynomial ring
    polynomials = [R(expr) for expr in substituted_expressions]
    #print(polynomials)    
    return polynomials

def symbolic_to_polynomial1(symbolic_expressions, R, k):
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
                        # Ensure we don't assign a value of 0
                        while random_value == 0:
                            random_value = int(k.random_element())
                        random_replacements[var_str] = random_value  # Assign non-zero random field element
                    substitutions[var] = random_replacements[var_str]
            
            # Substitute the 'r' variables with their corresponding random values
            substituted_expressions.append(expr.subs(substitutions))
        else:
            substituted_expressions.append(expr)
    #print(random_replacements)
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
        #print(symbolic_expressions)
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


def symbolic_to_polynomial3(symbolic_expressions, R, k):
    """
    Constructs polynomial ring elements from symbolic expressions.
    
    Args:
        symbolic_expressions (list): List of symbolic expressions.
        R (PolynomialRing): Polynomial ring where polynomials will be constructed.
        k (FiniteField): Finite field for random elements.

    Returns:
        list: A list of polynomials in the polynomial ring with random elements from k substituted for 'r' variables.
    """
    # Initialize the list of polynomials
    polynomials = []
    
    # Get the generators of the polynomial ring R (e.g., x1, x2, ..., xn)
    x_vars = R.gens()

    # Iterate over each symbolic expression
    for expr in symbolic_expressions:
        # Initialize an empty polynomial in the ring R
        poly = R(0)
        
        # Break down the expression into its terms
        for term in expr.operands():
            coeff = 1  # Start with a coefficient of 1
            
            # Parse each factor in the term
            for factor in term.operands():
                factor_str = str(factor)
                
                if factor_str.startswith('r'):  # If it is an 'r' variable
                    # Replace with a random element from the field k
                    random_element = k.random_element()
                    coeff *= random_element
                elif factor_str.startswith('x'):  # If it is an 'x' variable
                    # Get the corresponding generator in R
                    var_index = int(factor_str[1:]) - 1
                    coeff *= x_vars[var_index]
            
            # Add the term to the polynomial
            poly += coeff

        # Append the constructed polynomial to the list
        polynomials.append(poly)
    
    return polynomials






def private_to_public(F, k, n, m, order="deglex"):
    R = PolynomialRing(k, ["x%d" % i for i in range(1,n+1)], order=order)
    M = MatrixSpace(k, n)
    # Generate the secret transformation T.
    T = M.random_element()
    while not T.is_invertible():
        T = M.random_element()
    # Compose the central maps with T.
    #print("F")
    #print(F)    
    #print("T")
    #print(T)
    P = apply_transformation(T, F, R)
    return P, T


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
    #for f in F:
     #   print(f)
    Q = [poly_to_matrix(f) for f in F]
    for M in Q:
        n, _ = M.dimensions()
        if not M.submatrix(n-m, n-m).is_zero():
            return False
    return True

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
        poly = R(poly)
        new_poly = poly.subs({x_vars[i]: transformed_vars[i] for i in range(n)})
        transformed_L.append(new_poly)

    return transformed_L



def time_key_gen(q_range, n_range, m_range):
    import time
    time_dict = {}

    all_verify_private_syzygy=True
    all_is_central_map=True
    all_verify_public_syzygy=True

    for q in range(2, q_range+1):
        for m in range(2, m_range+1):
            for n in range(m+2, n_range+1):
                k=GF(q)
                x_vars = var(["x%d" % i for i in range(1, n+1)])
                R = PolynomialRing(k, ["x%d" % i for i in range(1, n + 1)], order="deglex")
                
                start_time = time.time()
                F_polys = [0] * m
                while any(poly == 0 for poly in F_polys):
                    F, L = generate_keys_with_dependency(k, n, m)
                    F_polys = symbolic_to_polynomial2(F, R, k)    #ZeroDivisionError: inverse of Mod(0, 2) does not exist
                    #print(F_polys)
                P, T = private_to_public(F_polys, k, n, m)
                end_time = time.time()

                time_taken = end_time - start_time
                time_dict[(q, m, n)] = time_taken
                #print(len(L), len(F_polys))
                print(f"Time taken for q={q}, m={m}, n={n}: {time_taken} seconds")

                if not verify_syzygy(L, F_polys, x_vars):
                    all_verify_private_syzygy=False

                if not is_central_map(F_polys, m):
                    all_is_central_map=False

                if not verify_syzygy(apply_transformation(T, L, R), P, x_vars):
                    all_verify_public_syzygy=False

    if all_verify_private_syzygy:
        print("All private keys contain a syzygy!")
    else:
        print("NOT all private keys contain a syzygy!")

    if all_is_central_map:
        print("All private keys are central maps!")
    else:
        print("NOT private all keys are central maps!")

    if all_verify_public_syzygy:
        print("All public keys contain a syzygy!")
    else:
        print("NOT all public keys contain a syzygy!")

    return time_dict


def three_dimensional_scatterplot(dictionary):
    import matplotlib.pyplot as plt
    from mpl_toolkits.mplot3d import Axes3D

    # Assuming dictionary is already populated
    q_values = [key[0] for key in dictionary.keys()]
    m_values = [key[1] for key in dictionary.keys()]
    n_values = [key[2] for key in dictionary.keys()]
    time_values = list(dictionary.values())

    fig = plt.figure()
    ax = fig.add_subplot(111, projection='3d')
    scatter = ax.scatter(q_values, m_values, n_values, c=time_values)

    ax.set_xlabel('q')
    ax.set_ylabel('m')
    ax.set_zlabel('n')

    colorbar = fig.colorbar(scatter)
    colorbar.set_label('Time taken')
    plt.show()




def prime_powers(limit):
    # Iterate through primes up to the square root of the limit (since p^2 should be <= limit)
    for p in primes(limit):
        power = 1
        while p^power <= limit:
            yield p^power
            power += 1

def time_key_gen(q,n,m):
    k=GF(q)

    start_time = time.time()
    start_cpu = time.process_time()

    F, L = generate_keys_with_dependency(k, n, m)
    P, T = private_to_public(F, k, n, m)


    end_cpu = time.process_time()
    end_time = time.time()

    time_taken = end_time - start_time
    cpu_time = end_cpu - start_cpu

    return F, L, P, T, time_taken, cpu_time

def time_multiple_ranges_key_gen(q_range, n_range):

    all_verify_private_syzygy=True
    all_is_central_map=True
    all_verify_public_syzygy=True

    time_dict = {}
    cpu_time_dict = {}

    pp = primes(q_range)

    for q in pp:
        for n in range(5, n_range+1, 5):
            k=GF(q)
            x_vars = var(["x%d" % i for i in range(1, n+1)])
            R = PolynomialRing(k, ["x%d" % i for i in range(1, n + 1)], order="deglex")

            m=2*n/5
            F, L, P, T, time_taken, cpu_time = time_key_gen(q,n,m)
            #print(L)
            time_dict[(q, n)] = time_taken
            cpu_time_dict[(q, n)] = cpu_time
            print(f"Time taken for q={q}, n={n}: {time_taken} seconds")
            print(f"CPU time taken for q={q}, n={n}: {cpu_time} seconds")

            if not verify_syzygy_symbolically(L, F, x_vars, q, R):
                all_verify_private_syzygy=False
                print('Private syzygy does not verify!')

            if not is_central_map(F, m):
                all_is_central_map=False
                print('F not central!')

            if not verify_syzygy_symbolically(apply_transformation(T, L, R), P, x_vars, q, R):
                all_verify_public_syzygy=False
                print('Public syzygy does not verify!')

    if all_verify_private_syzygy:
        print("All private keys contain a syzygy!")
    else:
        print("NOT all private keys contain a syzygy!")

    if all_is_central_map:
        print("All private keys are central maps!")
    else:
        print("NOT private all keys are central maps!")

    if all_verify_public_syzygy:
        print("All public keys contain a syzygy!")
    else:
        print("NOT all public keys contain a syzygy!")

    return time_dict, cpu_time_dict

time_dict, cpu_time_dict = time_multiple_ranges_key_gen(10,10)

print(time_dict)
print(cpu_time_dict)


def dict_to_latex_2d_table(data):
    # Extract unique values of q and n from the dictionary
    q_values = sorted(set(key[0] for key in data.keys()))
    n_values = sorted(set(key[1] for key in data.keys()))

    # Create LaTeX table
    latex_str = "\\begin{table}[ht]\n\\centering\n\\begin{tabular}{|c|" + "c|" * len(n_values) + "}\n\\hline\n"
    latex_str += "q $\\backslash$ n & " + " & ".join([str(n) for n in n_values]) + " \\\\\n\\hline\n"

    # Fill in the table with values from the dictionary
    for q in q_values:
        row = [f"{data.get((q, n), ''):.5f}" if (q, n) in data else "-" for n in n_values]
        latex_str += f"{q} & " + " & ".join(row) + " \\\\\n"

    latex_str += "\\hline\n\\end{tabular}\n\\caption{2D Table of Data for q and n}\n\\end{table}"

    return latex_str


# Generate the LaTeX table
latex_table = dict_to_latex_2d_table(cpu_time_dict)
print(latex_table)


