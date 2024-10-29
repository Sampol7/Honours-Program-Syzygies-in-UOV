from sage.all import *
import time

def generate_keys(k, n, m, order="deglex"):
    R = PolynomialRing(k, ["x%d" % i for i in range(1, n+1)], order=order)
    M = MatrixSpace(k, n)
    
    # Generate central maps.
    F = []
    for i in range(m):
        x = R.gens()
        f = 0
        while f == 0:  # Ensure f is not the zero polynomial, otherwise not homogeneous
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

    q=k.order()
    M, b = linear_system_to_matrix(linear_system, a_vars, q)
    matrix_rank = M.rank()

    solutions = []
    particular_soln = M.solve_right(b)
    #print(particular_soln)
    kernel = M.right_kernel()
    print(kernel)

    # Genereer een willekeurige oplossing
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
    L = solution_to_linear_polynomials(solution, x, m, n)
    print('L')
    print(L)


    return L



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
        L = find_linear_syzygy(F, k, n, m)

        counter += 1
        if any(poly!=R(0) for poly in L) :
            # If a syzygy is found, return the linear polynomials L1, ..., Lm
            return L, P, F, T



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
    #print(L[0].parent())
    #print(F[0].parent())
    # Ensure that the lengths of L and F are the same
    if len(L) != len(F):
        raise ValueError("Length of L and F must be the same")

    # Compute the sum L1 * F1 + L2 * F2 + ... + Lm * Fm
    syzygy_sum = sum(L[i] * F[i] for i in range(len(L)))
    #print(syzygy_sum)

    # Simplify the result
    syzygy_sum = syzygy_sum.reduce()
    #print(syzygy_sum)


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
    #print(R)
    #print(L[0].parent())
    x_vars = R.gens()  # Haal de variabelen (x1, x2, ..., xn) uit de polynoomring
    n = len(x_vars)    # Aantal variabelen

    # Stap 1: Bereken de beelden van de x-variabelen onder de transformatie T
    transformed_vars = [sum(T[i, j] * x_vars[j] for j in range(n)) for i in range(n)]
    #print(transformed_vars)
    # Stap 2: Vervang elke x_i in L(x) door T(x_i)
    transformed_L = []
    for poly in L:
        poly = R(poly)
        new_poly = poly.subs({x_vars[i]: transformed_vars[i] for i in range(n)})
        transformed_L.append(new_poly)

    return transformed_L


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


# # Example usage
k = GF(2)  # Finite field (can be modified)
n = 5  # Number of variables
m = 3  # Number of polynomials
x_vars = var(["x%d" % i for i in range(1, n+1)])
R = PolynomialRing(k, ["x%d" % i for i in range(1, n + 1)], order="deglex")

L, P, F, T = generate_keys_with_syzygy(k, n, m)


def count_variable_appearances(k, n, m, iterations):
    """
    Run the `generate_keys_with_syzygy` function multiple times and count the appearances of each variable `x_i`
    in the list of linear polynomials in `L`.

    Args:
    - k: The number of equations in the system.
    - n: The number of variables `x_i` to consider.
    - m: Other relevant parameter for `generate_keys_with_syzygy`.
    - iterations: The number of times to run the key generation.

    Returns:
    - A dictionary where keys are variable names (x1, x2, ..., xn) and values are the number of times the variable appeared.
    """
    from collections import defaultdict
    
    # Initialize a dictionary to store the counts for each variable x_i
    variable_count = defaultdict(int)
    
    # Loop to generate keys and count variable appearances
    for _ in range(iterations):
        # Run the key generation function
        L, P, F, T = generate_keys_with_syzygy(k, n, m)
        #print("Linear Syzygies Found: ", L)

        # Loop through the expressions in L
        for expr in L:
            # Check for each variable x_i in the range 1 to n
            for i in range(1, n + 1):
                variable_name = f'x{i}'
                # If the variable x_i appears in the expression, increase its count
                if str(expr).find(variable_name) != -1:
                    variable_count[variable_name] += 1

    # Return the counts of each variable
    return dict(variable_count)

# print(count_variable_appearances(k, n, m, 10))


print("Linear Syzygies Found: ", L)
print("Public Key: ", P)
print("Private Key: ", F)
print("Public Key: ", [poly_to_matrix(p) for p in P])
print("Private Key: ", [poly_to_matrix(f) for f in F])
print("Linear Transformation: ", T)

print("Syzygy Verifies Over R: ", verify_syzygy_symbolically(L, F, x_vars))
print("Syzygy Verifies Over R: ", verify_syzygy_symbolically(L, P, x_vars))

public_syzygy=apply_transformation(T, L, R)
print(public_syzygy)
print("Syzygy Verifies Over R: ", verify_syzygy_symbolically(public_syzygy, P, x_vars)) #public syzygy is equal to L(T(x))




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

    L, P, F, T = generate_keys_with_syzygy(k, n, m)

    end_cpu = time.process_time()
    end_time = time.time()

    time_taken = end_time - start_time
    cpu_time = end_cpu - start_cpu

    return L, P, F, T, time_taken, cpu_time

def time_multiple_ranges_key_gen(q_range, n_range):
    time_dict = {}
    cpu_time_dict = {}

    pp = primes(q_range)

    for q in pp:
        for n in range(5, n_range+1, 5):
            m=2*n/5
            L, P, F, T, time_taken, cpu_time = time_key_gen(q,n,m)
            print(F)
            time_dict[(q, n)] = time_taken
            cpu_time_dict[(q, n)] = cpu_time
            print(f"Time taken for q={q}, n={n}: {time_taken} seconds")
            print(f"CPU time taken for q={q}, n={n}: {cpu_time} seconds")

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
    latex_str += "q \\backslash n & " + " & ".join([str(n) for n in n_values]) + " \\\\\n\\hline\n"

    # Fill in the table with values from the dictionary
    for q in q_values:
        row = [f"{data.get((q, n), ''):.5f}" if (q, n) in data else "-" for n in n_values]
        latex_str += f"{q} & " + " & ".join(row) + " \\\\\n"

    latex_str += "\\hline\n\\end{tabular}\n\\caption{2D Table of Data for q and n}\n\\end{table}"

    return latex_str


# Generate the LaTeX table
latex_table = dict_to_latex_2d_table(cpu_time_dict)
print(latex_table)




















