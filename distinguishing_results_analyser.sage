import math

def manipulate_list(input_list):
    # Step 1: Calculate the mean of the list
    mean_value = sum(input_list) / len(input_list)
    print(mean_value)
    
    # Step 2: Divide the mean by 10,000
    mean_divided = mean_value / 10000
    print(mean_divided)
    
    # Step 3: Take the logarithm base 2 of the result
    if mean_divided > 0:
        log_result = math.log2(mean_divided)
    else:
        raise ValueError("Logarithm undefined for non-positive values.")
    
    return log_result

# Example usage:
example_list = [267, 293, 280, 266, 306, 273, 281, 275, 287, 307, 278]
result = manipulate_list(example_list)
print("Result:", result)


import numpy as np
from sympy import symbols, Matrix

def find_multivariate_polynomial(X1, X2, Y):
    """
    Finds a multivariate polynomial that maps two input lists X1, X2
    to the output list Y.
    
    Args:
    X1: First input list
    X2: Second input list
    Y: Output list
    
    Returns:
    The symbolic multivariate polynomial as a string.
    """
    # Ensure the inputs have the same length
    assert len(X1) == len(X2) == len(Y), "Input lists must have the same length"
    
    # Define the symbolic variables for the polynomial
    x1, x2 = symbols('x1 x2')
    
    # Create a matrix to represent the polynomial terms
    terms = []
    
    # Choose the degree of the polynomial (assumed degree 2 for simplicity, can be adjusted)
    for i in range(3):  # x1^0, x1^1, x1^2
        for j in range(2):  # x2^0, x2^1, x2^2
            terms.append(x1**i * x2**j)
    
    # Create the system of equations (Vandermonde-like matrix)
    A = []
    for x1_val, x2_val in zip(X1, X2):
        row = [term.subs({x1: x1_val, x2: x2_val}) for term in terms]
        A.append(row)
    
    # Convert A to numpy array for solving
    A = np.array(A, dtype=float)
    
    # Solve for the coefficients
    coeffs = np.linalg.lstsq(A, Y, rcond=None)[0]
    
    # Construct the symbolic polynomial
    polynomial = sum(c * term for c, term in zip(coeffs, terms))
    
    return polynomial

# Example usage:
n = [5,5,5,6,6,6,4,4]
m = [3,2,4,3,4,5,2,3]
Y = [-11.4803,-12.659,-9.2157,-16.747,-15.747, -15.747,-7.443,-5.143]

polynomial = find_multivariate_polynomial(n, m, Y)
print(f"The multivariate polynomial is: {polynomial}")


# Example usage:
n = [5,5,5,6,6,6,4,4]
m = [3,2,4,3,4,5,2,3]
Y = [-11.4803,-12.659,-9.2157,-16.747,-15.747, -15.747,-7.443,-5.143]

polynomial = find_multivariate_polynomial(n, m, Y)
print(f"The multivariate polynomial is: {polynomial}")
