#############################################
###Experiment 1
#############################################

from sage.all import *

runs=3
sum_rank=0
high_rank=0
low_rank=0
ranks=[]

for run in range(runs):
    print(run)
    # Define the finite field and polynomial ring in Sage
    q=5
    k = GF(q)

    # Define the number of polynomials m and variables n
    m = 4
    n = 10

    # Define the polynomial ring with both x and f variables
    R_full = PolynomialRing(k, ["x%d" % i for i in range(1, n+1)] + [f'f_{l}_{i}_{j}' for l in range(m) for i in range(n-m) for j in range(i, n)])
    x_full = R_full.gens()

    # Extract only the x variables from the full list of generators
    x_vars = x_full[:n]

    L = [sum([k.random_element() * x_vars[i] for i in range(n)]) for _ in range(m)]


    # Define the f variables separately
    f_vars = var([f'f_{l}_{i}_{j}' for l in range(m) for i in range(n-m) for j in range(i, n)])

    # Create m quadratic polynomials F1, ..., Fm, each with unknown coefficients f_ij
    F = []
    for l in range(m):
        f = 0
        for i in range(n - m):
            start_index = i
            for j in range(start_index, n):
                f += R_full(f'f_{l}_{i}_{j}') * x_vars[i] * x_vars[j]
        F.append(f)

    #print(F)

    # Generate the secret transformation T
    M = MatrixSpace(k, n)
    T = M.random_element()
    while not T.is_invertible():
        T = M.random_element()

    #print(T)

    # Step 3: Apply the transformation T by substitution on the x variables
    P = []
    for f in F:
        # Create the substitution list for each x variable
        substitution = {x_vars[i]: sum(T[i,j] * x_vars[j] for j in range(n)) for i in range(n)}
        
        # Apply the substitution to the polynomial f
        f_transformed = f.subs(substitution)
        
        P.append(f_transformed)

    #print(P)


    # Step 3: Set up the dependency equation: L1 * F1 + L2 * F2 + ... + Lm * Fm = 0
    dependency_eq = sum(L[i] * P[i] for i in range(m))
    #print("equation")
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
        f_vars = var([f'f_{l}_{i}_{j}' for l in range(m) for i in range(n-m) for j in range(i, n)])


        # Step 2: Parse the equation string into a symbolic expression and simplify
        polynomial = SR(str(eq)).expand()  # Expand the equation to combine like terms
        #print(polynomial)

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
    #print("system")
    #print(linear_system)



    def linear_system_to_matrix(equations, variables, k):
        """
        Transforms a system of linear equations into its corresponding matrix form.

        :param equations: List of linear equations.
        :param variables: List of variables to solve for.
        :return: Coefficient matrix and optionally the constant terms vector.
        """
        # Number of equations and variables
        num_equations = len(equations)
        num_variables = len(variables)

        print("Number of eq/var")
        print(num_equations)
        print(num_variables)

        print("Theoretical number of eq/var")
        print(((n+2)*(n+1)*n/6-(m+2)*(m+1)*m/6))
        print(m*((n+1)*n-(m+1)*m)/2)
        
        # Initialize an empty matrix to store coefficients
        A = matrix(k, num_equations, num_variables)  # Coefficient matrix
        
        # Loop through each equation to extract coefficients
        for i, eq in enumerate(equations):
            # Move all terms to the left-hand side
            eq = eq.lhs() - eq.rhs()
            
            # Extract coefficients for each variable
            for j, var in enumerate(variables):
                A[i, j] = eq.coefficient(var)
                
        return A

    M = linear_system_to_matrix(linear_system, f_vars, k)
    #print("matrix")
    #print(M)

    # Step 5: Compute the rank of the matrix M
    matrix_rank = M.rank()
    print("rank")
    print(matrix_rank)

    ranks.append(matrix_rank)


print('Experiment1:')

print('q')
print(q)

print('n')
print(n)

print('m')
print(m)

print('runs')
print(runs)

print('len(f_vars)')
print(len(f_vars))

print('sum_rank')
print(sum_rank)

print('low_rank')
print(low_rank)

print('high_rank')
print(high_rank)

print('ranks')
print(ranks)












