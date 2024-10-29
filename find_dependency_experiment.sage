import time

def generate_random_list(ring, n):
  """
  Generates a list of n random elements from the given ring.

  Args:
    ring: The ring to generate elements from.
    n: The number of random elements to generate.

  Returns:
    A list of n random elements from the ring.
  """
  k = ring.base_ring()
  return [k.random_element() for _ in range(n)]
  
def generate_private_keys_with_dependencies(k, n, m, order="deglex"):
    R = PolynomialRing(k, ["x%d" % i for i in range(1,n+1)], order=order)
    M = MatrixSpace(k, n)
    L_list = generate_random_list(R, m)
    while L_list[0]==0:
        L_list = generate_random_list(R, m)


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
    #print("F")
    #print(F)

    # Calculate the inverse of the coefficient of the first variable in L_list[0]
    # leading_coeff = L_list[0].coefficient(R.gens()[0])
    L_inv = 1 / L_list[0] # Calculate inverse of the coefficient
    F_1 = -L_list[1] * F[1]
    for i in range(2, m):
        F_1 -= L_list[i] * F[i]
    F_1 = L_inv*F_1
    #print("F_1")
    #print(F_1)
    F[0] = F_1  # Prepend F_1 to the list of polynomials F
    #print("F")
    #print(F)
    return F, L_list, x

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
    F, L_list, x = generate_private_keys_with_dependencies(k, n, m)
    P,T = private_to_public_key(F, k, n, m)
    return P, F, T, L_list, x




#######################################################################
##right_solve
#######################################################################
def find_dependency_using_right_solve(F, k, n, m):
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
  
    q=k.order()
    M, b = linear_system_to_matrix(linear_system, c_vars, q)
    matrix_rank = M.rank()

    solutions=[]
    particular_soln = M.solve_right(b)
    for homogeneous_soln in M.right_kernel():
        solution=particular_soln + homogeneous_soln
        solutions.append(solution)
    #print('solutions')
    #print(solutions)


    return solutions



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












#######################################################################
##test
#######################################################################

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



q=2
k=GF(q)
n=5
m=2

R = PolynomialRing(k, ["x%d" % i for i in range(1, n + 1)], order="deglex")

F, L, x = generate_private_keys_with_dependencies(k, n, m)

P, T = private_to_public_key(F, k, n, m)

L_prime = apply_transformation(T, L, R)
print("Original dependency:")
print(L_prime)

print("Original dependency verifies:")
print(verify_syzygy(L_prime, P, x))


L_right_solve = find_dependency_using_right_solve(P, k, n, m)
print("Found dependencies:")
print(L_right_solve)

all_verify=True
original_syzygy_found=False
for Li in L_right_solve:
    Li_prime = apply_transformation(T, Li, R)
    if not verify_syzygy(Li_prime, P, x):
        all_verify=False
    if tuple(L_prime) == tuple(Li_prime):
        original_syzygy_found=True
print("All found dependencies verify:")
print(all_verify)
print("Original syzygy is found:")
print(original_syzygy_found)


def time_dependency_finding(q,n,m):
    k=GF(q)

    F, L, x = generate_private_keys_with_dependencies(k, n, m)
    P, T = private_to_public_key(F, k, n, m)

    start_time = time.time()
    start_cpu = time.process_time()

    L_right_solve = find_dependency_using_right_solve(P, k, n, m)

    end_cpu = time.process_time()
    end_time = time.time()

    time_taken = end_time - start_time
    cpu_time = end_cpu - start_cpu

    return L_right_solve, L, P, F, T, time_taken, cpu_time


def time_multiple_ranges_key_gen(q_range, n_range):
    time_dict = {}
    cpu_time_dict = {}

    pp = primes(q_range)

    all_verify=True
    original_syzygy_found=False

    for q in pp:
        for n in range(5, n_range+1, 5):
            k=GF(q)
            R = PolynomialRing(k, ["x%d" % i for i in range(1, n + 1)], order="deglex")     
            x=R.gens()
            m=2*n/5
            L_right_solve, L, P, F, T, time_taken, cpu_time = time_dependency_finding(q,n,m)
            #print(F)
            time_dict[(q, n)] = time_taken
            cpu_time_dict[(q, n)] = cpu_time
            print(f"Time taken for q={q}, n={n}: {time_taken} seconds")
            print(f"CPU time taken for q={q}, n={n}: {cpu_time} seconds")


            for Li in L_right_solve:
                Li_prime=apply_transformation(T, Li, R)
                if not verify_syzygy(Li_prime, P, x):
                    all_verify=False
                if tuple(L_prime) == tuple(Li_prime):
                    original_syzygy_found=True

    return time_dict, cpu_time_dict

time_dict, cpu_time_dict = time_multiple_ranges_key_gen(15,30)

print("All found dependencies verify:")
print(all_verify)
print("Original syzygy is found:")
print(original_syzygy_found)

print(time_dict)
print(cpu_time_dict)


def dict_to_latex_2d_table(data):
    # Extract unique values of q and n from the dictionary
    q_values = sorted(set(key[0] for key in data.keys()))
    n_values = sorted(set(key[1] for key in data.keys()))

    # Create LaTeX table
    latex_str = "\\begin{table}[ht]\n\\centering\n\\begin{tabular}{|c|" + "c|" * len(n_values) + "}\n\\hline\n"
    latex_str += "q $\backslash$ n & " + " & ".join([str(n) for n in n_values]) + " \\\\\n\\hline\n"

    # Fill in the table with values from the dictionary
    for q in q_values:
        row = [f"{data.get((q, n), ''):.5f}" if (q, n) in data else "-" for n in n_values]
        latex_str += f"{q} & " + " & ".join(row) + " \\\\\n"

    latex_str += "\\hline\n\\end{tabular}\n\\caption{2D Table of Data for q and n}\n\\end{table}"

    return latex_str


# Generate the LaTeX table
latex_table = dict_to_latex_2d_table(cpu_time_dict)
print(latex_table)
