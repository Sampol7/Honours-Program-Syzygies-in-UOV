

# This file was *autogenerated* from the file timings_keygen.sage
from sage.all_cmdline import *   # import sage library

_sage_const_1 = Integer(1); _sage_const_0 = Integer(0); _sage_const_5 = Integer(5); _sage_const_2 = Integer(2); _sage_const_10 = Integer(10); _sage_const_30 = Integer(30)
import time

# generate_keys returns a random UOV instance (P, F, T) for the specified
# field k, number of variables n, and number of polynomials m.
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

    
def prime_powers(limit):
    # Iterate through primes up to the square root of the limit (since p^2 should be <= limit)
    for p in primes(limit):
        power = _sage_const_1 
        while p**power <= limit:
            yield p**power
            power += _sage_const_1 

def time_key_gen(q,n,m):
    k=GF(q)

    start_time = time.time()
    start_cpu = time.process_time()

    P, F, T = generate_keys(k,n,m)

    end_cpu = time.process_time()
    end_time = time.time()

    time_taken = end_time - start_time
    cpu_time = end_cpu - start_cpu

    return P, T, F, time_taken, cpu_time

def time_multiple_ranges_key_gen(q_range, n_range):
    time_dict = {}
    cpu_time_dict = {}

    pp = prime_powers(q_range)

    for q in pp:
        for n in range(_sage_const_5 , n_range+_sage_const_1 , _sage_const_5 ):
            m=_sage_const_2 *n/_sage_const_5 
            P, T, F, time_taken, cpu_time = time_key_gen(q,n,m)
            print(F)
            time_dict[(q, n)] = time_taken
            cpu_time_dict[(q, n)] = cpu_time
            print(f"Time taken for q={q}, n={n}: {time_taken} seconds")
            print(f"CPU time taken for q={q}, n={n}: {cpu_time} seconds")

    return time_dict, cpu_time_dict

time_dict, cpu_time_dict = time_multiple_ranges_key_gen(_sage_const_10 ,_sage_const_30 )

print(time_dict)
print(cpu_time_dict)


def dict_to_latex_2d_table(data):
    # Extract unique values of q and n from the dictionary
    q_values = sorted(set(key[_sage_const_0 ] for key in data.keys()))
    n_values = sorted(set(key[_sage_const_1 ] for key in data.keys()))

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

