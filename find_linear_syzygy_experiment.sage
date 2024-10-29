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

def private_to_public_key(F, k, n, m, order="deglex"):
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



#######################################################################
##right_solve
#######################################################################


def solution_to_linear_polynomials(solution, k, m, n):
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
    x=R.gens()

    # Initialize an empty list to store the linear polynomials
    linear_polynomials = []

    # Iterate over each linear polynomial L_i
    for i in range(m):
        linear_poly = 0  # Start with a zero polynomial for L_i

        # Iterate over each x_j variable and the corresponding coefficient a_i_j
        for j in range(n):
            # Extract the coefficient a_i_j from the solution
            linear_poly += R(solution[i*n+j]) * x[j]
        # Add the constructed linear polynomial to the list
        linear_polynomials.append(linear_poly)

    return linear_polynomials


def find_dependency_using_right_solve(F, k, n, m):
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
    dependency_eq = sum(L[i] * F[i] for i in range(m))
    # print("syzygy_eq")
    # print(str(syzygy_eq))

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
    M, b = linear_system_to_matrix(linear_system, a_vars, q)
    matrix_rank = M.rank()

    L_right_solve=[]
    particular_soln = M.solve_right(b)
    for homogeneous_soln in M.right_kernel():
        solution=particular_soln + homogeneous_soln
        L = solution_to_linear_polynomials(solution, k, m, n)
        L_right_solve.append(L)
    #print('solutions')
    #print(solutions)


    return L_right_solve



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

    #print('T')
    #print(T)
    # Stap 2: Vervang elke x_i in L(x) door T(x_i)
    transformed_L = []
    for poly in L:
        #print('poly')
        #print(poly)
        #print('R')       
        #print(R)
        poly = R(poly)
        new_poly = poly.subs({x_vars[i]: transformed_vars[i] for i in range(n)})
        transformed_L.append(new_poly)
        #print('transformed_L')
        #print(transformed_L)

    return transformed_L



q=2
k=GF(q)
n=5
m=2

R = PolynomialRing(k, ["x%d" % i for i in range(1, n + 1)], order="deglex")

F, L = generate_keys_with_dependency(k, n, m)

P, T = private_to_public_key(F, k, n, m)

L_prime=apply_transformation(T, L, R)
print("Original dependency:")
print(L_prime)

print("Original dependency verifies:")
print(verify_syzygy(L_prime, P, x))


L_right_solve = find_dependency_using_right_solve(P, k, n, m)
print("Found dependencies:")
print(L_right_solve)

R = PolynomialRing(k, ["x%d" % i for i in range(1, n + 1)], order="deglex")

all_verify=True
original_syzygy_found=False
for Li in L_right_solve:
    if not verify_syzygy(Li, P, x):
        all_verify=False
    if tuple(L_prime) == tuple(Li):
        original_syzygy_found=True
print("All found dependencies verify:")
print(all_verify)
print("Original syzygy is found:")
print(original_syzygy_found)


def time_dependency_finding(q,n,m):
    k=GF(q)
    R = PolynomialRing(k, ["x%d" % i for i in range(1, n + 1)], order="deglex")     

    F, L = generate_keys_with_dependency(k, n, m)
    P, T = private_to_public_key(F, k, n, m)

    L_prime=apply_transformation(T, L, R)


    start_time = time.time()
    start_cpu = time.process_time()

    L_right_solve = find_dependency_using_right_solve(P, k, n, m)

    end_cpu = time.process_time()
    end_time = time.time()

    time_taken = end_time - start_time
    cpu_time = end_cpu - start_cpu

    return L_right_solve, L_prime, P, F, T, time_taken, cpu_time


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
            L_right_solve, L_prime, P, F, T, time_taken, cpu_time = time_dependency_finding(q,n,m)
            #print(F)
            time_dict[(q, n)] = time_taken
            cpu_time_dict[(q, n)] = cpu_time
            print(f"Time taken for q={q}, n={n}: {time_taken} seconds")
            print(f"CPU time taken for q={q}, n={n}: {cpu_time} seconds")


            for Li in L_right_solve:
                if not verify_syzygy(Li, P, x):
                    all_verify=False
                if tuple(L_prime) == tuple(Li):
                    original_syzygy_found=True

    return time_dict, cpu_time_dict

time_dict, cpu_time_dict = time_multiple_ranges_key_gen(10,15)

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
