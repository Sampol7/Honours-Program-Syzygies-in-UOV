from sage.all import *

import time


# Key generation and common procedures for Unbalanced Oil and Vinegar.
# reset()

# generate_keys returns a random UOV instance (P, F, T) for the specified
# field k, number of variables n, and number of polynomials m.
def generate_keys(k, n, m, order="deglex"):
    R = PolynomialRing(k, ["x%d" % i for i in range(1,n+1)], order=order)
    M = MatrixSpace(k, n)
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
    # Generate the secret transformation T.
    T = M.random_element()
    while not T.is_invertible():
        T = M.random_element()
    # Compose the central maps with T.
    P = [T.act_on_polynomial(f) for f in F]
    return P, F, T

# is_central_map returns true if all elements of the specified list of
# matrices Q have zero submatrix corresponding to the oil variables.
def is_central_map(F, m):
    Q = [poly_to_matrix(f) for f in F]
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

# matrix_to_poly returns the polynomial corresponding to the quadratic form
# Q, where variables are formed by the generators of the polynomial ring R.
def matrix_to_poly(R, Q):
    x = vector(R.gens())
    return x * Q * x

# compose_qf returns a composition of the quadratic form Q with the linear
# transformation A.
def compose_qf(Q, A):
    if "matrix" in dir(A):
        A = A.matrix()
    return A.transpose() * Q * A

# subs replaces the variables of f with the components of the vector v. f can
# either be a polynomial or a matrix.
def subs(f, v):
    s = {}
    gens = f.parent().gens()
    if "submatrix" in dir(f):
        gens = f.base_ring().gens()
    for i in range(len(gens)):
        s[gens[i]] = v[i]
    return f.subs(s)

# polar_form returns the value of the polar form at (x, y).
def polar_form(f, x, y):
    return subs(f, x + y) - subs(f, x) - subs(f, y)

# find_solutions solves the multivariate quadratic system of equations
# specified by ideal I. All solutions are returned when dim I = 0. If
# dim I = 1 random linear constraints are added to reduce the dimension and
# the operation is retried. An empty list is returned when dim I > 1 or dim I
# < 0 (no solutions).
def find_solutions(I):
    dim = I.dimension()
    if dim < 0 or dim > 1:
        # print("find_solutions with dim(I) = %d; returning []" % dim)
        return []
    elif dim == 0:
        return I.variety()
    # dimension 1
    sols = []
    R = I.gen(0).parent()
    x_i = R.gen(randint(0, len(R.gens())-1))
    for val in I.base_ring():
        J = ideal(I.gens() + [x_i + val])
        sols += find_solutions(J)
    return sols

# invert_central_map returns a pre-image value a such that F(a) = b.
def invert_central_map(F_polys, b, debug=False):
    R_x = F_polys[0].parent()
    k = R_x.base_ring()
    n = len(R_x.gens())
    m = len(F_polys)
    # It should be possible to invert the central map in qˆ(n-m) attempts.
    for _ in range(k.order()**(n-m)):
        a = []
        fixed_vars = {}
        for i in range(n-m):
            v = k.random_element()
            fixed_vars[R_x.gen(i)] = v
            a.append(v)
        if debug: print("fixed_vars =", fixed_vars)
        F_prime = [f.subs(fixed_vars) for f in F_polys]
        if debug: print("F_prime =", F_prime)
        M = []
        for f in F_prime:
            row = []
            for i in range(n-m, n):
                row.append(f.monomial_coefficient(R_x.gen(i)))
            M.append(row)
        M = matrix(M)
        if debug:
            print("M =")
            pretty_print(M)
        if M.is_invertible():
            b_prime = []
            for i in range(len(F_prime)):
                v = F_prime[i].constant_coefficient()
                b_prime.append(b[i] - v)
            b_prime = vector(b_prime)
            if debug: print("b_prime =", b_prime)
            M_inv = M.inverse()
            sol = M_inv * b_prime
            a.extend(sol)
            return vector(a)
    # This may happen for small values of q, m, n.
    assert false, "failed to invert the central map (try a different key)"

# verify returns true if P(a) == b for all components of the public key P.
def verify(P, a, b):
    b_prime = vector([subs(p, a) for p in P])
    return b_prime == b

# sign returns a signature vector a such that P(a) = b, where P is the
# public key (P = F o T).
def sign(F, T, b):
    a = invert_central_map(F, b)
    return T.inverse() * a

# oilspace_y returns O_y = span(e_{n-m}, ..., e_n).
def oilspace_y(k, n, m):
    basis = []
    for i in range(m):
        v = [0 for j in range(n)]
        v[n - i - 1] = 1
        basis.append(v)
    return span(k, basis)

# oilspace_x returns O_x, which is a pre-image of O_y with respect to T.
def oilspace_x(n, m, T):
    k = T.base_ring()
    T_inv = T.inverse()
    basis = []
    for b in oilspace_y(k, n, m).basis():
        basis.append(T_inv * b)
    return span(k, basis)

# test_central_map ensures that the central map vanishes on O_y.
def test_central_map(F, num_tests=10):
    R = F[0].parent()
    k = R.base_ring()
    n = len(R.gens())
    m = len(F)
    O_y = oilspace_y(k, n, m)
    for i in range(num_tests):
        o = O_y.random_element()
        subs = {}
        for i in range(len(R.gens())):
            subs[R.gen(i)] = o[i]
        for i in range(len(F)):
            # print("F_%d(%s) = %s" % (i, subs, F[i].subs(subs)))
            assert F[i].subs(subs) == 0

# test_public_key ensures that the public key vanishes on the O_x.
def test_public_key(P, O_x, num_tests=10):
    R = P[0].parent()
    k = R.base_ring()
    for i in range(num_tests):
        v = O_x.random_element()
        subs = {}
        for i in range(len(v)):
            subs[R.gen(i)] = v[i]
        for i in range(len(v), len(R.gens())):
            subs[R.gen(i)] = 0
        for i in range(len(P)):
            # print("P_%d(%s) = %s" % (i, subs, P[i].subs(subs)))
            assert P[i].subs(subs) == 0

# test_poly_matrix verifies that the matrix to poly conversion works as
# expected.
def test_poly_matrix(polys):
    R = polys[0].parent()
    k = R.base_ring()
    n = len(R.gens())
    G = GL(n, k)
    for f in polys:
        # test poly/matrix conversions
        R = f.parent()
        Q = poly_to_matrix(f)
        g = matrix_to_poly(R, Q)
        assert f == g, "poly_matrix 1"
        # test group actions
        A = G.random_element()
        f = A.matrix().act_on_polynomial(f)
        Q = compose_qf(Q, A)
        g = matrix_to_poly(R, Q)
        assert f == g, "poly_matrix 2"

# define and execute a test suite for the UOV programs.
def run_tests():
    n = 5
    m = 2
    for q in [2, 3, 31]:
        k = GF(q, "z")
        P, F, T = generate_keys(k, n, m)
        O_x = oilspace_x(n, m, T)
        test_central_map(F)
        test_public_key(P, O_x)
        test_poly_matrix(F + P)
        Q = [poly_to_matrix(f) for f in F]
        assert is_central_map(Q, m)
        b = vector(k, [k.random_element() for i in range(m)])
        a = sign(F, T, b)
        assert verify(P, a, b), "sign/verify failed"
#run_tests()

# sign_verify_example generates a new set of keys, signs a message, and
# verifies the signature. It prints all the intermediate results.
def sign_verify_example():
    # Generate a new key pair
    P_polys, F_polys, A = generate_keys(GF(31), 5, 2)
    P = [poly_to_matrix(p, symmetric=False) for p in P_polys]
    F = [poly_to_matrix(f, symmetric=False) for f in F_polys]
    print("Central map")
    pretty_print(F)
    print("Public key")
    pretty_print(P)
    print("Secret linear transformation")
    pretty_print(A)
    # Invert the central map.
    mu = [7, 14]
    sigma_prime = invert_central_map(F_polys, mu, True)
    # Confirm the central map inverted correctly.
    print("Message =", mu)
    print("Pre-image of the central map =", sigma_prime)
    print("Evaluating F_polys at sigma_prime")
    for i in range(len(F)):
        res = sigma_prime * F[i] * sigma_prime
        print(" F_%d%s = %d" % (i, sigma_prime, res))
    # Invert the public key and confirm the inversion is successful.
    sigma = A.inverse()*sigma_prime
    print("Pre-image of the public key =", sigma)
    print("Evaluating P_polys at sigma")
    for i in range(len(P)):
        res = sigma * P[i] * sigma
        print(" P_%d%s = %d" % (i, sigma, res))

# permutation_example illustrates that a different choice of oil variables
# produces a polynomial with the properties similar to UOV central maps.
def pemutation_example():
    # Generate a random central map.
    k = GF(31)
    _, F_polys, _ = generate_keys(k, 5, 2)
    f = F_polys[0]
    F = poly_to_matrix(f)
    R = F_polys[0].parent()
    print("A randomly generated central map is given by")
    print("f =", f)
    print("The matrix form of f is F =")
    pretty_print(F)
    # The oil variables from Definition 2.0.3 are x_4 and x_5. We swap x_4
    # with x_2 using the following permutation matrix.
    M_pi = matrix(k, [[1, 0, 0, 0, 0],
    [0, 0, 0, 1, 0],
    [0, 0, 1, 0, 0],
    [0, 1, 0, 0, 0],
    [0, 0, 0, 0, 1]])
    # F_pi is no longer a central map as per Definition 2.0.3.
    F_pi = compose_qf(F, M_pi)
    print("Matrix of the central map F with x_4 and x_2 swapped is F_pi =")
    pretty_print(F_pi)
    # However, F_pi is linear in x_2, x_4, which can be inverted using
    # the same procedure as in Lemma 2.0.4.
    f_pi = matrix_to_poly(R, F_pi)
    print("The polynomial corresponding to F_pi is")
    print("f_pi =", f_pi)
    V = R.gens_dict()
    print("f_pi(1, x_2, 1, 1, x_5) =",
    f_pi.subs({V["x1"]: 1, V["x3"]: 1, V["x4"]: 1}))
    print("f (1, 1, 1, x_4, x_5) =",
    f.subs({V["x1"]: 1, V["x2"]: 1, V["x3"]: 1}))
# Example 1: generate keys, sign a message, verify the signature.
#
# sign_verify_example()
# Example 2: different choice of oil variables x_{n-m+1}, ..., x_n.
#
# pemutation_example()

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


def time_key_gen(q,n,m):
    k=GF(q)

    start_time = time.time()
    start_cpu = time.process_time()

    #F = [0] * m
    #retries=-1
    #while any(poly == 0 for poly in F):
        #F, L_list, x = generate_private_keys_with_dependencies(k, n, m)
        #retries+=1
    #print("retries")
    #print(retries)

    F, L_list, x = generate_private_keys_with_dependencies(k, n, m)

    P, T = private_to_public_key(F, k, n, m)
    end_time = time.time()
    end_cpu = time.process_time()

    time_taken = end_time - start_time
    cpu_time = end_cpu - start_cpu


    return P, F, T, L_list, x, time_taken, cpu_time




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


def prime_powers(limit):
    # Iterate through primes up to the square root of the limit (since p^2 should be <= limit)
    for p in primes(limit):
        power = 1
        while p^power <= limit:
            yield p^power
            power += 1

def time_q_range_key_gen(q_range, n, m):
    time_dict = {}

    pp = prime_powers(q_range)

    all_verify_private_syzygy=True
    all_is_central_map=True
    all_verify_public_syzygy=True

    for q in pp:
        k=GF(q)
        R = PolynomialRing(k, ["x%d" % i for i in range(1, n + 1)], order="deglex")
        
        P, F, T, L, variables, time_taken = time_key_gen(q, n, m)
        time_dict[(q, m, n)] = time_taken
        print(f"Time taken for q={q}, m={m}, n={n}: {time_taken} seconds")

        if not is_central_map(F, m):
            all_is_central_map=False

        if L is None or not verify_syzygy(L, F, variables):
            all_verify_private_syzygy=False

        if L is None or not verify_syzygy(apply_transformation(T, L, R), P, variables):
            all_verify_public_syzygy=False

    if all_is_central_map:
        print("All private keys are central maps!")
    else:
        print("NOT private all keys are central maps!") 

    if all_verify_private_syzygy:
        print("All private keys contain a syzygy!")
    else:
        print("NOT all private keys contain a syzygy!")

    if all_verify_public_syzygy:
        print("All public keys contain a syzygy!")
    else:
        print("NOT all public keys contain a syzygy!")

    return time_dict


def time_n_range_key_gen(q, n_range, m):
    time_dict = {}

    all_verify_private_syzygy=True
    all_is_central_map=True
    all_verify_public_syzygy=True

    for n in range(m+1, n_range+1):
        k=GF(q)
        R = PolynomialRing(k, ["x%d" % i for i in range(1, n + 1)], order="deglex")
        
        P, F, T, L, variables, time_taken = time_key_gen(q, n, m)
        time_dict[(q, m, n)] = time_taken
        print(f"Time taken for q={q}, m={m}, n={n}: {time_taken} seconds")

        if not is_central_map(F, m):
            all_is_central_map=False

        if L is None or not verify_syzygy(L, F, variables):
            all_verify_private_syzygy=False

        if L is None or not verify_syzygy(apply_transformation(T, L, R), P, variables):
            all_verify_public_syzygy=False

    if all_is_central_map:
        print("All private keys are central maps!")
    else:
        print("NOT private all keys are central maps!") 

    if all_verify_private_syzygy:
        print("All private keys contain a syzygy!")
    else:
        print("NOT all private keys contain a syzygy!")

    if all_verify_public_syzygy:
        print("All public keys contain a syzygy!")
    else:
        print("NOT all public keys contain a syzygy!")

    return time_dict



def time_m_range_key_gen(q, n, m_range):
    time_dict = {}

    all_verify_private_syzygy=True
    all_is_central_map=True
    all_verify_public_syzygy=True

    for m in range(3, m_range+1):
        k=GF(q)
        R = PolynomialRing(k, ["x%d" % i for i in range(1, n + 1)], order="deglex")

        P, F, T, L, variables, time_taken = time_key_gen(q, n, m)
        time_dict[(q, m, n)] = time_taken
        print(f"Time taken for q={q}, m={m}, n={n}: {time_taken} seconds")

        if not is_central_map(F, m):
            all_is_central_map=False

        if L is None or not verify_syzygy(L, F, variables):
            all_verify_private_syzygy=False

        if L is None or not verify_syzygy(apply_transformation(T, L, R), P, variables):
            all_verify_public_syzygy=False

    if all_is_central_map:
        print("All private keys are central maps!")
    else:
        print("NOT private all keys are central maps!") 

    if all_verify_private_syzygy:
        print("All private keys contain a syzygy!")
    else:
        print("NOT all private keys contain a syzygy!")

    if all_verify_public_syzygy:
        print("All public keys contain a syzygy!")
    else:
        print("NOT all public keys contain a syzygy!")

    return time_dict


def time_multiple_ranges_key_gen(q_range, n_range, m_range):
    time_dict = {}

    pp = prime_powers(q_range)

    all_verify_private_syzygy=True
    all_is_central_map=True
    all_verify_public_syzygy=True

    for q in pp:
        for m in range(3, m_range+1):
            for n in range(m+1, n_range+1):
                k=GF(q)
                R = PolynomialRing(k, ["x%d" % i for i in range(1, n + 1)], order="deglex")

                P, F, T, L, variables, time_taken = time_key_gen(q, n, m)
                time_dict[(q, m, n)] = time_taken
                print(f"Time taken for q={q}, m={m}, n={n}: {time_taken} seconds")

                if not is_central_map(F, m):
                    all_is_central_map=False

                if L is None or not verify_syzygy(L, F, variables):
                    all_verify_private_syzygy=False

                if L is None or not verify_syzygy(apply_transformation(T, L, R), P, variables):
                    all_verify_public_syzygy=False

    if all_is_central_map:
        print("All private keys are central maps!")
    else:
        print("NOT private all keys are central maps!") 

    if all_verify_private_syzygy:
        print("All private keys contain a syzygy!")
    else:
        print("NOT all private keys contain a syzygy!")

    if all_verify_public_syzygy:
        print("All public keys contain a syzygy!")
    else:
        print("NOT all public keys contain a syzygy!")

    return time_dict


#time_dict = time_q_range_key_gen(200, 10, 4)
#time_dict = time_n_range_key_gen(16, 40, 20)
#time_dict = time_m_range_key_gen(16, 40, 20)
#time_dict = time_multiple_ranges_key_gen(10, 10, 5)




def time_multiple_ranges_key_gen(q_range, n_range):
    time_dict = {}
    cpu_time_dict = {}

    pp = prime_powers(q_range)

    for q in pp:
        for n in range(5, n_range+1, 5):
            m=2*n/5
            P, F, T, L_list, x, time_taken, cpu_time = time_key_gen(q,n,m)
            #print(F)
            time_dict[(q, n)] = time_taken
            cpu_time_dict[(q, n)] = cpu_time
            print(f"Time taken for q={q}, n={n}: {time_taken} seconds")
            print(f"CPU time taken for q={q}, n={n}: {cpu_time} seconds")

    return time_dict, cpu_time_dict

time_dict, cpu_time_dict = time_multiple_ranges_key_gen(10,30)

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
