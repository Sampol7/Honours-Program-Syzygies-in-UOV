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
        print(F)
        print(P)
        P_polys.append(P)
        P_matrices.append([poly_to_matrix(p) for p in P])
    return P_polys, P_matrices

def generate_random_key(amount, k, n, m, order="deglex"):
    P_polys = []
    P_matrices = []
    for i in range(amount):
        P, F, T = generate_poly(k, n, m, order=order)
        print(F)
        print(P)
        P_polys.append(P)
        P_matrices.append([poly_to_matrix(p) for p in P])
    return P_polys, P_matrices



num_keys = 2
field = GF(7)
num_vars = 4
num_polys = 3

poly_keys, matrix_keys = generate_public_key(num_keys, field, num_vars, num_polys)
print(matrix_keys)
# Bekijk de gegenereerde UOV-public keys
for i, key in enumerate(matrix_keys):
    print(f"Key {i+1}:")
    for matrix in key:
        print(matrix)
        print()


poly_random, matrix_random = generate_random_key(num_keys, field, num_vars, num_polys)
# Bekijk de gegenereerde UOV-public keys
for i, key in enumerate(matrix_random):
    print(f"Key {i+1}:")
    for matrix in key:
        print(matrix)
        print()



import numpy as np

from scipy.stats import pearsonr # Removed the unexpected indentation


def is_uov_key(keys):
    # Lijst om alle coëfficiënten te verzamelen (lijst van matrices, 1 matrix per polynoom)
    all_coeffs = []
    for key in keys:
        # Transposeer elke matrix en voeg toe aan all_coeffs
        for matrix in key:
            all_coeffs.append(np.array(matrix).T.astype(float)) # Convert elements to float

    # Zet alle coëfficiënten in een numpy-array voor eenvoudiger verwerking
    all_coeffs = np.array(all_coeffs)

    # Bereken de correlatie tussen elke paar kolommen (coëfficiënten van dezelfde polynomen)
    num_cols = all_coeffs.shape[2]  # Aangepast naar de juiste dimensie
    correlations = []

    for i in range(num_cols):
        for j in range(i + 1, num_cols):
            # Flatten the arrays before calculating correlation
            corr, _ = pearsonr(all_coeffs[:, :, i].flatten(), all_coeffs[:, :, j].flatten())
            correlations.append(corr)

    # Analyseer de correlaties
    avg_corr = np.mean(correlations)
    print(avg_corr)
    # Als de gemiddelde correlatie significant groter is dan 0, beschouw het als UOV
    if avg_corr > 0.2:  # Deze drempelwaarde kan worden aangepast na testing
        return "UOV"
    else:
        return "Random"



# Voer de correlatieanalyse uit
result = is_uov_key(matrix_keys)
print("Real: UOV")
print("Predicted:")
print(result)

result = is_uov_key(matrix_random)
print("Real: Random")
print("Predicted:")
print(result)









def is_uov_key_oil_vinegar(keys, vinegar_vars, oil_vars):
    """
    Voert analyse van olie-azijn interacties uit om te bepalen of gegeven sleutels representaties zijn van publieke UOV-polynomen of random stelsels.
    
    Args:
    - keys: Een lijst van UOV-public key matrixvoorstellingen (lijst van lijsten van matrices).
    - oil_vars: Aantal olievariabelen (de eerste oil_vars variabelen zijn olie).
    - vinegar_vars: Aantal azijnvariabelen (de laatste vinegar_vars variabelen zijn azijn).
    
    Returns:
    - 'UOV' als de sleutels waarschijnlijk representaties zijn van publieke UOV-polynomen,
      'Random' als de sleutels waarschijnlijk random zijn.
    """
    
    # Controleer op consistentie van olie en azijn variabelen
    total_vars = oil_vars + vinegar_vars
    if total_vars <= 0:
        raise ValueError("Het totaal aantal olie- en azijnvariabelen moet positief zijn.")

    oil_azijn_interacties = 0
    oil_oil_interacties = 0

    # Loop over alle sleutels (lijsten van matrices)
    for key in keys:
        for matrix in key:
            # Loop door de entries van de matrix
            for i in range(total_vars):
                for j in range(total_vars):
                    # Use matrix[i][j] to access elements in SageMath Matrix
                    if matrix[i][j] != 0:  # Alleen als de interactie niet nul is
                        if i < oil_vars and j < oil_vars:
                            # Olie-olie interactie
                            oil_oil_interacties += 1
                        elif (i < oil_vars and j >= oil_vars) or (i >= oil_vars and j < oil_vars):
                            # Olie-azijn interactie
                            oil_azijn_interacties += 1

    # Bereken de verhouding olie-azijn vs olie-olie interacties
    if oil_oil_interacties == 0:  # Vermijd deling door nul
        oil_oil_interacties = 1

    print(oil_azijn_interacties)
    print(oil_oil_interacties)
    interactie_ratio = oil_azijn_interacties / oil_oil_interacties

    # Stel een drempelwaarde in voor deze verhouding om UOV vs random te onderscheiden
    # Publieke UOV-sleutels hebben over het algemeen veel meer olie-azijn interacties dan olie-olie interacties.
    if interactie_ratio > 2.0:  # Deze drempelwaarde kan aangepast worden na verdere analyse
        return "UOV"
    else:
        return "Random"




# Voer de olie-azijn interactieanalyse uit
result = is_uov_key_oil_vinegar(matrix_keys, num_vars-num_polys, num_polys)
print("Real: UOV")
print("Predicted:")
print(result)

result = is_uov_key_oil_vinegar(matrix_random, num_vars-num_polys, num_polys)
print("Real: Random")
print("Predicted:")
print(result)



def is_uov_key_solution_space_dimension(generated_keys, num_oil, num_polys):
    """
    Function to check if the solution space dimension suggests a UOV key.
    
    Args:
    - generated_keys: List of keys (each represented as matrices).
    - num_oil: Number of oil variables.
    - num_polys: Number of polynomials (same as the number of central maps).
    
    Returns:
    - True if the keys are likely UOV keys based on the solution space dimension.
    """
    for key in generated_keys:
        solution_space_dims = []
        for matrix in key:
            # Create symbolic variables
            x = [var(f'x{i+1}') for i in range(num_oil + num_polys)]
            
            # Set up the equation system
            equations = []
            for i in range(num_oil + num_polys):
                eq = 0
                for j in range(i, num_oil + num_polys):
                    eq += SR(matrix[i, j]) * x[i] * x[j]  # Convert matrix element to symbolic
                equations.append(eq)
            
            # Solve the system symbolically
            sol_space = solve(equations, x)
            solution_space_dims.append(len(sol_space))
        
        # Perform a check on the solution space dimension
        if not all(dim == expected_dimension for dim in solution_space_dims):
            return False
    return True



# Voer de analyse van oplossingsruimte-dimensie uit
result = is_uov_key_solution_space_dimension(matrix_keys, num_vars-num_polys, num_polys)
print("Real: UOV")
print("Predicted:")
print(result)

result = is_uov_key_solution_space_dimension(matrix_random, num_vars-num_polys, num_polys)
print("Real: Random")
print("Predicted:")
print(result)