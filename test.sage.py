

# This file was *autogenerated* from the file test.sage
from sage.all_cmdline import *   # import sage library

_sage_const_1 = Integer(1); _sage_const_0 = Integer(0); _sage_const_2 = Integer(2); _sage_const_0p8 = RealNumber('0.8'); _sage_const_0p5 = RealNumber('0.5'); _sage_const_0p35 = RealNumber('0.35'); _sage_const_0p00001 = RealNumber('0.00001'); _sage_const_4 = Integer(4); _sage_const_10 = Integer(10); _sage_const_5 = Integer(5); _sage_const_7 = Integer(7); _sage_const_3 = Integer(3)
from sage.all import *

def generate_keys(k, n, m, order="deglex"):
    R = PolynomialRing(k, ["x%d" % i for i in range(_sage_const_1 ,n+_sage_const_1 )], order=order)
    M = MatrixSpace(k, n)
    # Generate central maps.
    F = []
    for i in range(m):
        x = R.gens()
        f = _sage_const_0 
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
    R = PolynomialRing(k, ["x%d" % i for i in range(_sage_const_1 , n+_sage_const_1 )] + [f'a_{i}_{j}' for i in range(m) for j in range(n)])
    x = R.gens()[:n]  # Get the x variables (x1, ..., xn)
    a = R.gens()[n:]  # Get the a_ij variables

    x_vars = var(["x%d" % i for i in range(_sage_const_1 , n+_sage_const_1 )])  # Define the variables for x1, x2, ..., xn
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
        R = PolynomialRing(k, ["x%d" % i for i in range(_sage_const_1 , n+_sage_const_1 )]) # Include a_ij variables
        x = R.gens()

        x_vars = var(["x%d" % i for i in range(_sage_const_1 , n+_sage_const_1 )])  # Define the variables for x1, x2, ..., xn
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
            coeff = term.subs({x:_sage_const_1  for x in x_vars})
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
            equation = coeff == _sage_const_0   # Set the sum of coefficients to zero
            linear_system.append(equation)
        return linear_system

    # Step 5: Construct the linear system from the syzygy equation
    linear_system = construct_linear_system_from_syzygy(syzygy_eq, n, m)

    R = PolynomialRing(k, ["x%d" % i for i in range(_sage_const_1 , n+_sage_const_1 )] + [f'a_{i}_{j}' for i in range(m) for j in range(n)])

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
        if equation.rhs() != _sage_const_0 : # Access the right-hand side of the equation to check the value
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

def generate_keys_with_syzygy(k, n, m, order="deglex"):
    """
    Continuously generate UOV keys using generate_keys() and check for linear syzygies.
    If a syzygy is found, return the linear polynomials L1, ..., Lm.
    """
    counter = _sage_const_0 
    while True:
        print(counter)
        # Generate UOV keys using the generate_keys function
        P, F, T = generate_keys(k, n, m, order)

        # Check if a linear syzygy exists in the generated keys
        L = find_linear_syzygy(P, k, n, m)

        counter += _sage_const_1 

        if L != None:
            # If a syzygy is found, return the linear polynomials L1, ..., Lm
            return L, P, F, T

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
        linear_poly = _sage_const_0   # Start with a zero polynomial for L_i

        # Iterate over each x_j variable and the corresponding coefficient a_i_j
        for j in range(n):
            # Extract the coefficient a_i_j from the solution
            coeff = None
            for eq in solution:
                if eq.lhs() == var(f'a_{i}_{j}'):
                    coeff = eq.rhs()  # Get the right-hand side value (the coefficient)
                    break

            # Add the term coeff * x_j to the linear polynomial (if coeff is not zero)
            if coeff != _sage_const_0 :
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

    if syzygy_sum == _sage_const_0 :
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

    if syzygy_sum == _sage_const_0 :
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
            substituted_expressions.append(expr.subs({var: _sage_const_1  for var in expr.variables() if str(var).startswith('r')}))
        else:
            # Directly append the integer/constant term
            substituted_expressions.append(expr)

    # Convert the substituted expressions into elements of the polynomial ring
    polynomials = [R(expr) for expr in substituted_expressions]
    
    return polynomials


import numpy as np


def MonomialsOfDegree(ring, degree):
    """
    Generates a list of all monomials of a given degree in a polynomial ring.

    Args:
        ring: The polynomial ring.
        degree: The desired degree of monomials.

    Returns:
        list: A list of monomials of the specified degree.
    """
    result = []
    variables = ring.gens()
    num_vars = len(variables)

    def generate(index, current_monomial, current_degree):
        if index == num_vars:
            if current_degree == degree:
                result.append(current_monomial)
            return

        for i in range(degree - current_degree + _sage_const_1 ):
            new_monomial = current_monomial * variables[index]**i
            generate(index + _sage_const_1 , new_monomial, current_degree + i)

    generate(_sage_const_0 , ring(_sage_const_1 ), _sage_const_0 )
    return result


def generate_keys_with_syzygies(k, n, m, syzygy_degree=_sage_const_1 , num_syzygies=_sage_const_1 , order="deglex"):
    """
    Generates a UOV key pair with a specified number of syzygies of a given degree.

    Args:
        k: The base field.
        n: The number of variables.
        m: The number of polynomials.
        syzygy_degree: The degree of the syzygies to include.
        num_syzygies: The number of syzygies to include.
        order: The monomial order (default is "deglex").

    Returns:
        P (list): The public key polynomials.
        F (list): The private key polynomials (central map).
        T (Matrix): The secret transformation matrix.
    """
    # Step 1: Define the polynomial ring
    R = PolynomialRing(k, ["x%d" % i for i in range(_sage_const_1 , n + _sage_const_1 )], order=order)
    M = MatrixSpace(k, n)

    # Step 2: Generate central maps with syzygies
    F = []
    for i in range(m - num_syzygies):
        x = R.gens()
        f = _sage_const_0 
        for i in range(n - m):
            start_index = i
            for j in range(start_index, n):
                f += k.random_element() * x[i] * x[j]
        F.append(f)

    # Step 3: Generate syzygies and corresponding polynomials
    syzygies = []
    for _ in range(num_syzygies):
        L = []
        for i in range(m):
            L_i = _sage_const_0 
            for mon in MonomialsOfDegree(R, syzygy_degree):
                L_i += k.random_element() * mon
            L.append(L_i)
        syzygies.append(L)

        # Construct F_i that satisfy the syzygy L_1 * F_1 + ... + L_m * F_m = 0
        syzygy_polynomial = sum(L[i] * F[i] for i in range(len(F)))
        F.append(-syzygy_polynomial)

    # Step 4: Generate the secret transformation T
    T = M.random_element()
    while not T.is_invertible():
        T = M.random_element()

    # Step 5: Compose the central maps with T to create the public key
    P = [T.act_on_polynomial(f) for f in F]

    return P, F, T, syzygies, x


# Construct the Coefficient Matrix
def construct_coefficient_matrix(syzygies, n):
    """
    Constructs the coefficient matrix from the given syzygies.

    Args:
        syzygies (list): The syzygies generated in Step 1.
        n (int): The number of variables.

    Returns:
        Matrix: The coefficient matrix M.
    """
    R = syzygies[_sage_const_0 ][_sage_const_0 ].parent()
    variables = R.gens()
    coefficient_matrix = []

    for L in syzygies:
        for L_i in L:
            coefficients = [L_i.coefficient(v) for v in variables]
            coefficient_matrix.append(coefficients)

    return Matrix(coefficient_matrix)








# Rank Analysis
def rank_analysis(M, variables):
    full_rank = M.rank()

    potential_oil_vars = []
    for var_subset in Subsets(variables, len(variables) - _sage_const_1 ):
        indices = [variables.index(v) for v in var_subset]
        submatrix = M.matrix_from_columns(indices)
        sub_rank = submatrix.rank()
        if sub_rank < full_rank:
            potential_oil_vars.append(var_subset)

    return potential_oil_vars

# Frequency Analysis
def frequency_analysis(M, variables):
    freq_counts = [sum(_sage_const_1  for x in M.column(j) if x != _sage_const_0 ) for j in range(len(variables))] # Count non-zero entries in each column
    sorted_vars = sorted(zip(freq_counts, variables), reverse=True)

    # Assuming 2 oil variables; you can adjust this as needed
    likely_oil_vars = [var for _, var in sorted_vars[:_sage_const_2 ]]
    return likely_oil_vars

def correlation_analysis(M, variables, threshold=_sage_const_0p8 ):
    """
    Perform correlation analysis on the coefficient matrix to identify potential oil variables.

    Args:
        M (Matrix): The matrix where each row corresponds to the coefficients
                                     of variables in the syzygies.
        variables (list): A list of variable names corresponding to the columns of the matrix.
        threshold (float): The correlation threshold to consider variables as correlated.
                           Default is 0.8.

    Returns:
        correlated_variables (list): A list of sets, each containing pairs of variables that are
                                     highly correlated and thus potential oil variables.
    """
    # Calculate the number of variables
    num_vars = M.ncols()

    # Initialize a list to store sets of correlated variables
    correlated_variables = []

    # Compute the correlation matrix
    correlation_matrix = M.transpose() * M

    # Normalize the correlation matrix (Modified to handle polynomial entries)
    for i in range(num_vars):
        for j in range(num_vars):
            norm_factor_squared = correlation_matrix[i,i] * correlation_matrix[j,j]
            # Check if the norm factor squared is a perfect square
            if is_perfect_square(norm_factor_squared):
                norm_factor = sqrt(norm_factor_squared)
                # Handle potential zero division
                if norm_factor != _sage_const_0 :
                    correlation_matrix[i, j] /= norm_factor

    # Analyze the correlation matrix (Use .lc() to get leading coefficient and handle finite field elements)
    for i in range(num_vars):
        for j in range(i + _sage_const_1 , num_vars):
            # Calculate the 'magnitude' of the correlation in the finite field
            correlation_value = correlation_matrix[i, j].lc()
            # You might need to define a suitable metric for 'magnitude' in your finite field
            # For example, you could use the absolute value of the integer representation of the field element
            magnitude = abs(int(correlation_value))
            if magnitude >= threshold * int(k.order()): # Scale threshold by the field order
                correlated_variables.append((variables[i], variables[j]))

    return correlated_variables

def is_perfect_square(poly):
    """
    Checks if a given polynomial is a perfect square in the polynomial ring.

    Args:
        poly: The polynomial to check.

    Returns:
        bool: True if the polynomial is a perfect square, False otherwise.
    """
    R = poly.parent()
    try:
        sqrt_poly = R(poly).sqrt()
        return sqrt_poly * sqrt_poly == poly
    except:
        return False

def sparse_representation_analysis(coefficient_matrix, variables, sparsity_threshold=_sage_const_0p5 ):
    """
    Perform sparse representation analysis on the coefficient matrix to identify potential oil variables.

    Args:
        coefficient_matrix (Matrix): The matrix where each row corresponds to the coefficients
                                     of variables in the syzygies.
        variables (list): A list of variable names corresponding to the columns of the matrix.
        sparsity_threshold (float): The threshold ratio for considering a variable to be involved in a sparse
                                    representation. Default is 0.5.

    Returns:
        potential_oil_variables (list): A list of variables that are involved in sparse representations
                                        and are thus potential oil variables.
    """
    # Number of syzygies and variables
    num_syzygies, num_vars = coefficient_matrix.nrows(), coefficient_matrix.ncols()

    # Initialize a list to store variables involved in sparse representations
    potential_oil_variables = []

    # Analyze each column (variable) for sparsity
    for j in range(num_vars):
        non_zero_count = _sage_const_0 

        # Count the number of non-zero coefficients for this variable across all syzygies
        for i in range(num_syzygies):
            if coefficient_matrix[i, j] != _sage_const_0 :
                non_zero_count += _sage_const_1 

        # Calculate sparsity ratio
        sparsity_ratio = non_zero_count / num_syzygies

        # If the sparsity ratio is below the threshold, consider this variable as a potential oil variable
        if sparsity_ratio <= sparsity_threshold:
            potential_oil_variables.append(variables[j])

    return potential_oil_variables

def pca_analysis(coefficient_matrix, variables, num_components=_sage_const_2 , contribution_threshold=_sage_const_0p35 ):
    """
    Perform Principal Component Analysis (PCA) on the coefficient matrix to identify potential oil variables.

    Args:
        coefficient_matrix (Matrix): The matrix where each row corresponds to the coefficients
                                     of variables in the syzygies.
        variables (list): A list of variable names corresponding to the columns of the matrix.
        num_components (int): The number of principal components to consider. Default is 2.
        contribution_threshold (float): The threshold for considering a variable as contributing
                                        significantly to a principal component. Default is 0.1.

    Returns:
        potential_oil_variables (list): A list of variables that contribute significantly to the first
                                        few principal components and are thus potential oil variables.
    """
    # Convert the SageMath matrix to a NumPy array for SVD computation
    # Extract the leading coefficients of the polynomials to get numerical values
    # Use `int()` to convert finite field elements to integers
    numerical_matrix = np.array([[int(entry.lc()) for entry in row] for row in coefficient_matrix])  # Convert to integer representation

    # Perform PCA using Singular Value Decomposition (SVD) on the numerical matrix
    U, S, Vt = np.linalg.svd(numerical_matrix)

    # Get the principal components (rows of Vt correspond to principal components)
    principal_components = Vt[:num_components]

    # Initialize a list to store variables that contribute significantly to the principal components
    potential_oil_variables = []

    # Analyze the contribution of each variable to the principal components
    for j in range(coefficient_matrix.ncols()):
        for i in range(num_components):
            if abs(principal_components[i, j]) > contribution_threshold:
                potential_oil_variables.append(variables[j])
                break  # If the variable contributes to any of the components, we add it

    return list(set(potential_oil_variables))  # Return unique variables

from scipy.cluster.hierarchy import linkage, fcluster
from scipy.spatial.distance import pdist

def cluster_analysis(coefficient_matrix, variables, num_clusters=_sage_const_2 ):
    """
    Perform Cluster Analysis on the coefficient matrix to identify potential oil variables.

    Args:
        coefficient_matrix (Matrix): The matrix where each row corresponds to the coefficients
                                     of variables in the syzygies.
        variables (list): A list of variable names corresponding to the columns of the matrix.
        num_clusters (int): The number of clusters to form. Default is 2.

    Returns:
        potential_oil_variables (list): A list of variables that are grouped into clusters
                                        potentially corresponding to oil variables.
    """
    # Convert the SageMath matrix to a NumPy array for compatibility with scipy functions
    # Extract leading coefficients and convert them to integers for numerical processing
    coefficient_array = np.array([[int(entry.lc()) for entry in row]
                                  for row in coefficient_matrix])

    # Compute the pairwise distances between variables (columns of the coefficient matrix)
    distances = pdist(coefficient_array.T, 'euclidean')

    # Perform hierarchical/agglomerative clustering
    Z = linkage(distances, method='ward')

    # Form clusters
    clusters = fcluster(Z, num_clusters, criterion='maxclust')

    # Identify potential oil variables as those in smaller clusters
    cluster_sizes = {i: _sage_const_0  for i in range(_sage_const_1 , num_clusters + _sage_const_1 )}
    for cluster_id in clusters:
        cluster_sizes[cluster_id] += _sage_const_1 

    # Find clusters that are smaller than others (potential oil variables)
    min_cluster_size = min(cluster_sizes.values())
    potential_oil_clusters = [cluster_id for cluster_id, size in cluster_sizes.items() if size == min_cluster_size]

    # Get the variables belonging to these small clusters
    potential_oil_variables = [variables[i] for i in range(len(variables)) if clusters[i] in potential_oil_clusters]

    return potential_oil_variables


def graph_analysis(coefficient_matrix, variables, connection_threshold=_sage_const_1 ):
    """
    Perform Syzygy Graph Analysis on the coefficient matrix to identify potential oil variables.

    Args:
        coefficient_matrix (Matrix): The matrix where each row corresponds to the coefficients
                                     of variables in the syzygies.
        variables (list): A list of variable names corresponding to the columns of the matrix.
        connection_threshold (int): The maximum number of connections (edges) for a variable
                                    to be considered a potential oil variable. Default is 1.

    Returns:
        potential_oil_variables (list): A list of variables that have fewer connections in the
                                        syzygy graph and are thus potential oil variables.
    """
    # Number of variables
    num_vars = len(variables)

    # Initialize an empty graph
    G = Graph()

    # Add vertices for each variable
    G.add_vertices(variables)

    # Add edges between variables that appear together in a syzygy
    for i in range(coefficient_matrix.nrows()):
        involved_vars = [variables[j] for j in range(num_vars) if coefficient_matrix[i, j] != _sage_const_0 ]
        for v1 in involved_vars:
            for v2 in involved_vars:
                if v1 != v2 and not G.has_edge(v1, v2):
                    G.add_edge(v1, v2)

    # Identify potential oil variables based on their degree in the graph
    potential_oil_variables = []
    for v in G.vertices():
        if G.degree(v) <= connection_threshold:
            potential_oil_variables.append(v)

    return potential_oil_variables


def linear_programming_analysis(coefficient_matrix, variables, threshold=_sage_const_0p00001 ):
    """
    Perform Linear Programming Analysis on the coefficient matrix to identify potential oil variables.

    Args:
        coefficient_matrix (Matrix): The matrix where each row corresponds to the coefficients
                                     of variables in the syzygies.
        variables (list): A list of variable names corresponding to the columns of the matrix.

    Returns:
        potential_oil_variables (list): A list of variables that are identified as potential oil variables
                                        based on the solution to the linear programming problem.
    """
    # Number of variables
    num_vars = len(variables)

    # Initialize the linear programming problem
    lp = MixedIntegerLinearProgram(maximization=False)

    # Define the variables for the LP problem (one for each syzygy)
    lp_vars = lp.new_variable(nonnegative=True)

    # Add the constraints from the coefficient matrix
    for i in range(coefficient_matrix.nrows()):
        # Sum of coefficients times variables <= 0 (for simplicity, assume less than or equal constraint)
        lp.add_constraint(sum(coefficient_matrix[i, j] * lp_vars[j] for j in range(num_vars)) <= _sage_const_0 )

    # Objective function: Minimize the sum of all variables
    lp.set_objective(lp.sum(lp_vars[j] for j in range(num_vars)))

    # Solve the LP problem
    try:
        lp.solve()
    except MIPSolverException:
        return "No solution found for the LP problem."

    # Get the values of the variables in the LP solution
    solution_values = [lp.get_values(lp_vars[j]) for j in range(num_vars)]

    # Analyze the solution to identify potential oil variables
    potential_oil_variables = []
    for i, value in enumerate(solution_values):
        # Heuristic: Variables with very small values might be considered potential oil variables
        if value < threshold:  # Threshold can be adjusted based on the problem
            potential_oil_variables.append(variables[i])

    return potential_oil_variables

import numpy as np
from scipy.stats import entropy

def entropy_based_analysis(coefficient_matrix, variables):
    """
    Perform Entropy-Based Analysis on the coefficient matrix to identify potential oil variables.

    Args:
        coefficient_matrix (Matrix): The matrix where each row corresponds to the coefficients
                                     of variables in the syzygies.
        variables (list): A list of variable names corresponding to the columns of the matrix.

    Returns:
        potential_oil_variables (list): A list of variables identified as potential oil variables
                                        based on their entropy values.
    """
    # Convert the SageMath matrix to a NumPy array for easier processing
    # Extract the leading coefficients of the polynomials to get numerical values
    # Use `int()` to convert finite field elements to integers
    coefficient_array = np.array([[int(entry.lc()) for entry in row] for row in coefficient_matrix])  # Extract leading coefficients and convert to integers

    # Calculate entropy for each variable (column)
    entropy_values = []
    for j in range(coefficient_array.shape[_sage_const_1 ]):
        # Normalize the coefficients in the column to form a probability distribution
        col = np.abs(coefficient_array[:, j])  # Now apply abs() to numerical values
        col_prob = col / col.sum() if col.sum() != _sage_const_0  else np.zeros_like(col)

        # Calculate entropy of the column
        ent_value = entropy(col_prob, base=_sage_const_2 )
        entropy_values.append(ent_value)

    # Identify potential oil variables: those with lower entropy
    avg_entropy = np.mean(entropy_values)
    potential_oil_variables = [variables[j] for j, ent in enumerate(entropy_values) if ent < avg_entropy]

    return potential_oil_variables

def boolean_analysis(coefficient_matrix, variables):
    """
    Perform Boolean Analysis on the coefficient matrix to identify potential oil variables.

    Args:
        coefficient_matrix (Matrix): The matrix where each row corresponds to the coefficients
                                     of variables in the syzygies.
        variables (list): A list of variable names corresponding to the columns of the matrix.

    Returns:
        potential_oil_variables (list): A list of variables identified as potential oil variables
                                        based on Boolean Analysis.
    """
    # Convert the coefficient matrix to a Boolean matrix (1 for non-zero, 0 for zero)
    boolean_matrix = coefficient_matrix.apply_map(lambda x: _sage_const_1  if x != _sage_const_0  else _sage_const_0 )

    # Analyze the Boolean matrix
    variable_scores = []
    for j in range(boolean_matrix.ncols()):
        # Count the number of syzygies (rows) in which the variable (column) appears (has a '1')
        score = sum(boolean_matrix[:, j])
        variable_scores.append(score)

    # Identify potential oil variables: those that appear in fewer syzygies
    avg_score = sum(variable_scores) / len(variable_scores)
    potential_oil_variables = [variables[j] for j, score in enumerate(variable_scores) if score < avg_score]

    return potential_oil_variables

def network_flow_analysis(coefficient_matrix, variables):
    """
    Perform Network Flow Analysis on the coefficient matrix to identify potential oil variables.

    Args:
        coefficient_matrix (Matrix): The matrix where each row corresponds to the coefficients
                                     of variables in the syzygies.
        variables (list): A list of variable names corresponding to the columns of the matrix.

    Returns:
        potential_oil_variables (list): A list of variables identified as potential oil variables
                                        based on network flow analysis.
    """
    # from sage.graphs.network_flow import NetworkFlow

    # Number of variables
    num_vars = len(variables)

    # Create a network flow graph, use DiGraph for directed graph
    G = DiGraph() # Change here to create a directed graph

    # Add nodes for each variable
    for var in variables:
        G.add_vertex(var)

    # Add edges between variables based on their presence in syzygies
    for i in range(coefficient_matrix.nrows()):
        involved_vars = [variables[j] for j in range(num_vars) if coefficient_matrix[i, j] != _sage_const_0 ]
        for v1 in involved_vars:
            for v2 in involved_vars:
                if v1 != v2:
                    if not G.has_edge(v1, v2):
                        G.add_edge(v1, v2)

    # Compute the network flow
    flow_dict = {}
    for vertex in G.vertices():
        flow_dict[vertex] = G.degree(vertex)

    # Identify potential oil variables: those with lower flow (degree)
    avg_flow = np.mean(list(flow_dict.values()))
    potential_oil_variables = [v for v in G.vertices() if flow_dict[v] < avg_flow]

    return potential_oil_variables

def machine_learning_analysis(coefficient_matrix, variables, num_clusters=_sage_const_4 ):
    """
    Perform Machine Learning Analysis using K-Means Clustering on the coefficient matrix
    to identify potential oil variables.

    Args:
        coefficient_matrix (Matrix): The matrix where each row corresponds to the coefficients
                                     of variables in the syzygies.
        variables (list): A list of variable names corresponding to the columns of the matrix.
        num_clusters (int): Number of clusters for K-Means (default is 2).

    Returns:
        potential_oil_variables (list): A list of variables identified as potential oil variables
                                        based on clustering analysis.
    """
    import numpy as np
    from sklearn.cluster import KMeans

    # Convert SageMath matrix to NumPy array and extract leading coefficients as integers
    coeff_array = np.array([[int(entry.lc()) for entry in row] for row in coefficient_matrix])

    # Transpose matrix to have variables as rows (features)
    coeff_array_T = coeff_array.T

    # Perform K-Means clustering
    kmeans = KMeans(n_clusters=num_clusters, random_state=_sage_const_0 , n_init=_sage_const_10 )  # Set n_init to 10
    kmeans.fit(coeff_array_T)
    labels = kmeans.labels_

    # Analyze clusters to identify potential oil variables
    # Extract leading coefficients from cluster means (if they are polynomials)
    cluster_means = [np.mean([int(entry.lc()) if isinstance(entry, sage.rings.polynomial.multi_polynomial_libsingular.MPolynomial_libsingular) else entry
                               for entry in coeff_array_T[labels == i]], axis=_sage_const_0 )
                     for i in range(num_clusters)]

    # Find the cluster with the least mean sum of absolute values
    mean_sums = [np.sum(np.abs(mean)) for mean in cluster_means]
    oil_cluster = np.argmin(mean_sums)

    # Variables in the oil cluster
    potential_oil_variables = [variables[i] for i, label in enumerate(labels) if label == oil_cluster]

    return potential_oil_variables


# Identify Oil Variables
def identify_oil_variables(F, syzygies, variables):
    print("F")
    print(F)
    print("syzygies")
    print(syzygies)
    M = construct_coefficient_matrix(syzygies, _sage_const_5 )
    print("M")
    print(M)
    potential_oil_vars_rank = rank_analysis(M, variables)
    print("potential_oil_vars_rank")
    print(potential_oil_vars_rank)
    likely_oil_vars_freq = frequency_analysis(M, variables)
    print("likely_oil_vars_freq")
    print(likely_oil_vars_freq)
    likely_oil_vars_corr = correlation_analysis(M, variables)
    print("likely_oil_vars_corr")
    print(likely_oil_vars_corr)
    likely_oil_vars_sparse = sparse_representation_analysis(M, variables)
    print("likely_oil_vars_sparse")
    print(likely_oil_vars_sparse)
    likely_oil_vars_pca = pca_analysis(M, variables)
    print("likely_oil_vars_pca")
    print(likely_oil_vars_pca)
    likely_oil_vars_cluster = cluster_analysis(M, variables)
    print("likely_oil_vars_cluster")
    print(likely_oil_vars_cluster)
    likely_oil_vars_graph = graph_analysis(M, variables)
    print("likely_oil_vars_graph")
    print(likely_oil_vars_graph)
    likely_oil_vars_lp = linear_programming_analysis(M, variables)
    print("likely_oil_vars_lp")
    print(likely_oil_vars_lp)
    likely_oil_vars_entropy = entropy_based_analysis(M, variables)
    print("likely_oil_vars_entropy")
    print(likely_oil_vars_entropy)
    likely_oil_vars_bool = boolean_analysis(M, variables)
    print("likely_oil_vars_bool")
    print(likely_oil_vars_bool)
    likely_oil_vars_flow = network_flow_analysis(M, variables)
    print("likely_oil_vars_flow")
    print(likely_oil_vars_flow)
    likely_oil_vars_ml = machine_learning_analysis(M, variables)
    print("likely_oil_vars_ml")
    print(likely_oil_vars_ml)

    final_oil_candidates = set()
    for subset in potential_oil_vars_rank:
        if all(var in likely_oil_vars_freq for var in subset):
            final_oil_candidates.update(subset)

    return final_oil_candidates

# Combine with the key generation function
def generate_keys_with_syzygies_and_identify_oil(k, n, m, syzygy_degree=_sage_const_1 , num_syzygies=_sage_const_1 , order="deglex"):
    """
    Generates a UOV key pair with a specified number of syzygies of a given degree, and identifies oil variables.

    Args:
        k: The base field.
        n: The number of variables.
        m: The number of polynomials.
        syzygy_degree: The degree of the syzygies to include.
        num_syzygies: The number of syzygies to include.
        order: The monomial order (default is "deglex").

    Returns:
        P (list): The public key polynomials.
        F (list): The private key polynomials (central map).
        T (Matrix): The secret transformation matrix.
        oil_vars (set): The identified oil variables.
    """
    # Generate keys with syzygies
    P, F, T, syzygies, variables = generate_keys_with_syzygies(k, n, m, syzygy_degree, num_syzygies, order)
    print(syzygies)
    print(variables)
    # Identify oil variables
    oil_vars = identify_oil_variables(P, syzygies, variables)

    return P, F, T, oil_vars



# Example usage
k = GF(_sage_const_2 )  # Finite field (can be modified)
n = _sage_const_7   # Number of variables
m = _sage_const_3   # Number of polynomials
x_vars = var(["x%d" % i for i in range(_sage_const_1 , n+_sage_const_1 )])
R = PolynomialRing(k, ["x%d" % i for i in range(_sage_const_1 , n + _sage_const_1 )], order="deglex")

L, P, F, T = generate_keys_with_syzygy(k, n, m)

oil_vars = identify_oil_variables(P, [symbolic_to_polynomial(L,R)], R.gens())


print("Oil variables are likely:", oil_vars)

