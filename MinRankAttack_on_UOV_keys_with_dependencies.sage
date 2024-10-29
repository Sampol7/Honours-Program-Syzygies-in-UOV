#!/usr/bin/env sage -python
# -*- coding: utf-8 -*-

"""Various utilities used throughout the MinRank implementation."""

import hashlib
from sage.all import *

__author__ = "Dario Gjorgjevski"
__email__ = "gjorgjevski.dario@students.finki.ukim.mk"
__license__ = "GPLv3"


def linear_combination(coeffs, elems):
    """Calculates a linear combination of elements given coefficients.

    Args:
        alpha: The coefficients.
        elems: The elements to combine.

    Returns:
        The linear combination of all elements given the coefficients.
    """
    return sum([coeff * elem for coeff, elem in zip(coeffs, elems)])


def random_full_rank_matrix(ring, nrows, ncols=None):
    """Generates a random, full-rank matrix over a specified ring.

    Args:
        ring: The ring over which to generate the matrix.
        nrows: The number of rows.
        ncols: The number of columns (if missing, matrix is made square).

    Returns:
        A random, full-rank matrix over a specified ring.
    """
    if ncols is None:
        ncols = nrows

    return random_matrix(ring, nrows, ncols,
                         algorithm='echelonizable',
                         rank=min(nrows, ncols))


# def sha256_hash(obj):
#     """Calculates a SHA256 digest of a Python object's representation.

#     Args:
#         obj: The object whose digest is to be calculated.

#     Returns:
#         The SHA256 digest of the object.
#     """
#     try:  # Use the str method on Sage objects if possible.
#         return hashlib.sha256(obj.str()).digest()
#     except:  # Else, fall back to the default repr function.
#         return hashlib.sha256(repr(obj)).digest()

def sha256_hash(obj):
    """Computes the SHA256 hash of an object.

    Args:
        obj: The object to be hashed.

    Returns:
        The SHA256 hash of the object.
    """
    # Sage matrices have a str method.
    try:
        # Check if the object is a tuple
        if isinstance(obj, tuple):
            # If it is a tuple, convert each element to bytes and join them
            return hashlib.sha256(b''.join([bytes(str(item), 'utf-8') for item in obj])).digest()
        else:
            # If it's not a tuple, use the str method on Sage objects if possible
            return hashlib.sha256(obj.str().encode('utf-8')).digest()
    except:
        # Else, fall back to the default repr function and encode as UTF-8
        return hashlib.sha256(repr(obj).encode('utf-8')).digest()


#!/usr/bin/env sage -python
# -*- coding: utf-8 -*-

"""Various algebraic attacks on the MinRank problem.

1) Kernel attack;
2) Groebner basis attack;
3) XL attack.

Example usage:
  >>> from mr_auth import MinRankInstance
  >>> MR = MinRankInstance(6, 5, 4, 3, 2)
  >>> A = MinRankAttack(MR)
  >>> A.run_groebner()
"""

from itertools import chain
from sage.all import *
from sage.rings.polynomial.multi_polynomial_sequence import *

__author__ = "Dario Gjorgjevski"
__email__ = "gjorgjevski.dario@students.finki.ukim.mk"
__license__ = "GPLv3"


class MinRankAttack(object):
    """A class allowing the execution of various attacks on a MR instance.

    Attributes:
        MR: The MinRank instance associated to this object.
    """
    def __init__(self, MR):
        """Initialized a MinRankAttack object.

        Args:
            MR: The MinRank instance that we wish to attack.
        """
        self.__MR = MR

    @property
    def MR(self):
        """Returns the associated MinRank instance."""
        return self.__MR

    @MR.setter
    def MR(self, MR):
        """Updates the associated MinRank instance."""
        self.__MR = MR

    @staticmethod
    def __run_kernel(MR, constrained_run):
        vs = [var('y' + str(i)) for i in range(MR.m)]
        attempts = 0

        # Use this to ensure that the system is never underdetermined.
        determinedness = ceil(MR.m / MR.eta)

        while not constrained_run or attempts < q**(determinedness * MR.r):
            xs = [random_vector(MR.finite_field, MR.n)
                  for _ in range(determinedness)]
            lhs = matrix(MR.finite_field, MR.eta * determinedness, MR.m,
                         [expr.coefficient(v)
                          for exprs in [linear_combination(vs, MR.matrices) * x
                                        for x in xs]
                          for expr in exprs
                          for v in vs])
            rhs = vector(MR.finite_field,
                         chain(
                             *[(MR.offset_matrix * x).list()
                               for x in xs]
                         ))
            try:
                # The general solution is always of the form
                # particular + homogeneous.
                p_soln = lhs.solve_right(rhs)
                for h_soln in lhs.right_kernel():
                    # Check for correctness.
                    if (linear_combination(p_soln + h_soln, MR.matrices) -
                            MR.offset_matrix).rank() <= MR.r:
                        return p_soln + h_soln
            except ValueError:
                pass  # Ignore if system could not be solved.
            finally:
                attempts += 1

        return None  # Nothing could be found.

    def run_kernel(self, constrained_run=False):
        """Performs a kernel attack on MR (Courtois & Goubin).

        Repeatedly guesses vectors with hopes they fall into the nullspace.
        Under the assumption that they do, solve the corresponding linear
        system.

        Args:
            constrained_run: Run the attack only for a limited number of
                times (default False).

        Returns:
            A vector giving a solution to the MinRank instance.  If the
            constrained_run parameter is True, then the value is None in
            case no solution could be found.
        """
        return self.__run_kernel(self.__MR, constrained_run)

    @staticmethod
    def __generate_MQ_system(MR):
        """Generates an MQ system associated to a MR instance."""
        # Form the variable names.
        xs = ['x' + str(j) + '_' + str(i)
              for i in range(MR.r)
              for j in range(MR.n - MR.r)]
        ys = ['y_' + str(i) for i in range(MR.m)]

        # Create the lex-ordered polynomial ring GF(q)[vars].
        R = PolynomialRing(MR.finite_field, names=(xs + ys))
        vs = R.gens()
        xs = vs[:(MR.r * (MR.n - MR.r))]
        ys = vs[(MR.r * (MR.n - MR.r)):]

        # Form the matrices.
        lhs = linear_combination(ys, MR.matrices) - MR.offset_matrix
        rhs = matrix(R, MR.n, MR.n - MR.r,
                     chain(
                         identity_matrix(R, MR.n - MR.r).list(),
                         list(xs)
                     ))

        # Return the system and the corresponding polynomial ring.
        return lhs * rhs, R

    def run_groebner(self):
        """Attacks MR by computing a Groebner basis (Kipnis & Shamir).

        Forms a multivariate quadratic (MQ) system corresponding to a MinRank
        instance.  Attempts to solve the system using built-in Sage functions.

        Returns:
            A solution to the MQ system giving a solution to the MR instance
            at the same time.

        Raises:
            AssertionError: The generated ideal is not radical.
        """
        # Form the system.
        system, R = self.__generate_MQ_system(self.__MR)
        PS = PolynomialSequence(system, R)

        # Maybe we can fix some variables and still expect a solution?
        delta = (self.__MR.r - self.__MR.eta) * (self.__MR.n - self.__MR.r) + \
            self.__MR.m
        if delta > 0:
            PS = PS.subs({v: 0 for v in R.gens()[:delta]})

        # Form the ideal, making sure everything's OK.  The field equations
        # are added to the ideal to make sure that it is radical.
        I = R.ideal(*PS) + \
            sage.rings.ideal.FieldIdeal(R)

        # assert I.dimension() in (-1, 0)
        assert I.radical() == I

        # R is a lex-ordered polynomial ring.  What the FGLM algorithm
        # does is it computes a Groebner basis with respect to a degrevlex
        # ordering and then converts it back to lex.
        I = R.ideal(I.groebner_basis(algorithm='libsingular:stdfglm'))

        # Return the affine variety.  This should be computationally cheap
        # since the ideal is generated by a lex Groebner basis.  Furthermore,
        # note that the previous addition of the field equations does not
        # change the affine variety whatsoever.
        return I.variety(I.base_ring())

    @staticmethod
    def __run_xl(PS, D):
        def generate_monomials(R, deg):
            """Generates all monomials over R of a given degree."""
            return [R({tuple(degs): 1})
                    for degs in WeightedIntegerVectors(
                            deg, [1 for _ in range(R.ngens())]
                    )]

        def solve(PS, offset=0, soln=None):
            """Tries to solve the system after it has been run through XL."""
            if soln is None:
                soln = {}

            if len(soln) == PS.ring().ngens():  # Found a solution.
                return soln

            for i in range(offset, len(PS)):
                PS = PS.subs(soln)  # Substitute what we have so far.
                if PS[i].is_constant():
                    if PS[i] == 0:  # 0 == 0.  OK.
                        continue
                    else:  # Inconsistent.
                        return None

                if not PS[i].is_univariate():  # Multivariate.
                    continue

                # Found an univaraite polynomial.  Find its roots.
                roots = PS[i].univariate_polynomial().roots(
                    multiplicities=False
                )

                for root in roots:  # Try to solve for each root.
                    new_soln = soln.copy()
                    new_soln[PS[i].variable(0)] = root
                    result = solve(PS, soln=new_soln)

                    if result is not None:
                        return result

            return None  # Found nothing.

        # Do the eXtended Linearization (XL) step.
        PS = PolynomialSequence(
            PS.ring().change_ring(order='lex'),  # Ensure lex ordering.
            chain(
                [m * p
                 for p in PS
                 for m in generate_monomials(PS.ring(), D - 2)],
                PS
            )
        )
        # Do the Gaussian elimination step.
        A, v = PS.coefficient_matrix(sparse=False)
        PS = PolynomialSequence(A.echelon_form() * v)
        # Solve.
        return solve(PS, offset=A.nrows() - A.rank())

    def run_xl(self, D):
        """Attacks MR by using the XL algorithm (Courtois et al).

        Args:
            D: The degree parameter (>= 2) used in the linearization.

        Raises:
            AssertionError: Invalid degree parameter.
        """
        assert D >= 2
        system, R = self.__generate_MQ_system(self.__MR)
        return self.__run_xl(PolynomialSequence(R, system), D)

    def __str__(self):
        """Pretty printing."""
        return "MinRankAttack object.  Associated MR instance: " + \
            str(self.__MR) + "."


#!/usr/bin/env sage -python
# -*- coding: utf-8 -*-

"""Zero-knowledge authentication protocol based on MinRank.

This file provides a toy implementation of a zero-knowledge authentication
protocol based on the MinRank problem from linear algebra.  It is written
as coursework at the Faculty of Computer Science and Engineering in
Skopje, Republic of Macedonia.  The protocol was proposed by
Nicolas T. Courtois; see https://eprint.iacr.org/2001/058.pdf for details.

Example usage:
  >>> MR = MinRankInstance(m, eta, n, r, q)
  >>> V = Verifier(MR)
  >>> P = Prover(MR)
  >>> authentication_driver(P, V)  # This prover should be rejected.
  >>> LP = LegitimateProver(MR)
  >>> MR.give_access(LP)
  >>> authentication_dirver(LP, V)  # This prover should _not_ be rejected.
"""

from copy import deepcopy
from sage.all import *

__author__ = "Dario Gjorgjevski"
__email__ = "gjorgjevski.dario@students.finki.ukim.mk"
__license__ = "GPLv3"

# Recommended number of rounds.
rounds = 35


class ProverNotReadyError(Exception):
    """An Exception to signify that a Prover is not ready."""
    pass


class VerifierNotReadyError(Exception):
    """An Exception to signify that a Verifier is not ready."""
    pass


class AuthenticationError(Exception):
    """An Exception to signify failed authentication."""
    pass

# def sha256_hash(obj):
#     """Computes the SHA256 hash of an object.

#     Args:
#         obj: The object to be hashed.

#     Returns:
#         The SHA256 hash of the object.
#     """
#     # Sage matrices have a str method.
#     try:
#         # Check if the object is a tuple
#         if isinstance(obj, tuple):
#             # If it is a tuple, convert each element to bytes and join them
#             return hashlib.sha256(b''.join([bytes(str(item), 'utf-8') for item in obj])).digest()
#         else:
#             # If it's not a tuple, use the str method on Sage objects if possible
#             return hashlib.sha256(obj.str().encode('utf-8')).digest()
#     except:
#         # Else, fall back to the default repr function and encode as UTF-8
#         return hashlib.sha256(repr(obj).encode('utf-8')).digest()


class Prover(object):
    """Prover class."""
    def __init__(self, MR):
        """Initializes a (naive) Prover object.

        Args:
            MR: The MR instance associated to the prover.
        """
        self._MR = MR  # Don't mangle names to allow for potential inheritance.
        self.__ready = False
        self.__awaiting_query = False

    @property
    def alpha(self):
        """Tries to compute a value for the secret vector alpha.

        This is a naive implementation which simply guesses alpha.
        Subclasses can override it and implement custom behavior.
        """
        try:
            return self.__alpha
        except AttributeError:
            self.__alpha = random_vector(self._MR.finite_field, self._MR.m)
            return self.__alpha

    def prepare_round(self):
        """Prepares a Prover object for a round of authentication."""
        # Generate the (S, T, X) triple.
        # S and T are generated as full rank eta x eta and n x n
        # matrices respectively.
        # X is a completely random eta x n matrix.
        S = random_full_rank_matrix(self._MR.finite_field, self._MR.eta)
        T = random_full_rank_matrix(self._MR.finite_field, self._MR.n)
        X = random_matrix(self._MR.finite_field,
                          self._MR.eta, self._MR.n)

        # Generate beta_1 and N_1.
        beta_1 = random_vector(self._MR.finite_field, self._MR.m)
        N_1 = linear_combination(beta_1, self._MR.matrices)

        # Generate beta_2 and N_2.
        beta_2 = self.alpha + beta_1
        N_2 = linear_combination(beta_2, self._MR.matrices)

        # These will all be used in the authentication; compute and store them.
        self.__STX = (S, T, X)
        self.__ID = (S * N_1 * T + X,
                     S * N_2 * T + X - S * self._MR.offset_matrix * T)
        self.__N = (N_1, N_2)
        self.__beta = (beta_1, beta_2)
        self.__ready = True

    def send_hashes(self, verifier):
        """Initialize the authentication by sending hashes to a Verifier.

        Args:
            verifier: A Verifier object that will perform the authentication.

        Raises:
            ProverNotReadyError: There is something that Prover still has not
                computed.
        """
        if not self.__ready:
            raise ProverNotReadyError("Prover has not computed STX and ID.")

        verifier.receive_hashes(*map(sha256_hash,
                                     (self.__STX,) + self.__ID))

        # Reset.
        self.__ready = False
        self.__awaiting_query = True

    def receive_query(self, verifier, Q):
        """Responds to a query presented by a Verifier.

        Args:
            verifier: The verifier to whom the response will be sent.
            Q: The query ID.

        Raises:
            ValueError: Invalid query ID.
        """
        if Q not in (0, 1, 2):
            raise ValueError(
                "Prover was prompted by Verifier with an invalid query."
            )
        elif not self.__awaiting_query:
            raise ProverNotReadyError(
                "Prover was not expecting a query but received one."
            )

        self.__awaiting_query = False  # Reset.

        if Q == 0:
            verifier.receive_response(Q, *self.__ID)
        elif Q == 1 or Q == 2:
            verifier.receive_response(Q, self.__STX, self.__beta[Q - 1])

    def __str__(self):
        """Pretty printing."""
        return "(Naive) Prover object.  Associated MR instance: " + \
            str(self._MR) + "."


class LegitimateProver(Prover):
    """A Legitimate Prover, i.e. one that holds a private key."""
    def __init__(self, MR, alpha=None):
        """Initializes a LegitimateProver object.

        A LegitimateProver should always authenticate successfully.
        Authentication is disallowed if either no or an incorrect
        secret vector is provided.

        Args:
            MR: The associated MinRank instance.
            alpha: The secret vector (optional).  Must be a solution
                to the associated MR instance.
        """
        super(LegitimateProver, self).__init__(MR)

        if alpha is not None:
            self.alpha = alpha

    def __check_alpha(self, alpha):
        """Checks if a given secret vector satisfies the associated MR."""
        return ((linear_combination(alpha, self._MR.matrices) -
                 self._MR.offset_matrix).rank() == self._MR.r)

    @property
    def alpha(self):
        """Computes (simply returns) the secret vector."""
        try:
            return self.__alpha
        except AttributeError:
            raise ProverNotReadyError(
                "LegitimateProver has no access to its secret vector."
            )

    @alpha.setter
    def alpha(self, alpha):
        """Receives the secret vector to a MR instance.

        Raises:
            ValueError: The secret vector is not a MR solution.
        """
        if not self.__check_alpha(alpha):
            raise ValueError("Attempt to give an invalid secret vector.")

        self.__alpha = alpha

    def __str__(self):
        """Pretty printing."""
        return "LegitimateProver object.  Associated MR instance: " + \
            str(self._MR) + "."


class Verifier(object):
    """Verifier class."""
    def __init__(self, MR):
        """Initializes a Verifier object.

        Args:
            MR: The MinRank instance associated to this verifier.
        """
        self.__MR = MR
        self.__has_hashes = False
        self.__awaiting_response = False

    def receive_hashes(self, STX_hash, ID_1_hash, ID_2_hash):
        """Receive hashes sent by a Prover.

        Args:
            STX_hash: The hash of the (S, T, X) triple.
            ID_1_hash: The hash of the first part of the Prover's ID.
            ID_2_hash: The hash of the second part of the Prover's ID.
        """
        self.__STX_hash = STX_hash
        self.__ID_hash = (ID_1_hash, ID_2_hash)
        self.__has_hashes = True

    def send_query(self, prover):
        """Sends a random query to a Prover and prompts for response.

        Args:
            prover: The prover that will be queried.

        Raises:
            HashesNotAvailableError: The Prover has not supplied hashes.
        """
        # Check if hashes are readily available.
        if not self.__has_hashes:
            raise VerifierNotReadyError(
                "Hashes must be sent to Verifier before any query is made."
            )
        # Prompt the prover for a response.
        self.__awaiting_response = True
        prover.receive_query(self, ZZ.random_element(0, 3))
        # Reset.
        self.__has_hashes = False

    def receive_response(self, Q, *args):
        """Receives and and processes a response sent by a Prover.

        Args:
            Q: The ID of the response.
            args: The contents of the response.  Meaning varies depending on
                response's ID.  If Q == 0, args is the Prover's ID.
                If Q == 1 or Q == 2, args[0] is the (S, T, X) triple and
                args[1] is the beta_Q vector.

        Raises:
            AuthenticationError: Unsuccessful authentication.
            VauleError: Invalid response ID.
        """
        if Q not in (0, 1, 2):
            raise ValueError("Invalid response type sent to Verifier.")
        elif not self.__awaiting_response:
            raise VerifierNotReadyError(
                "Verifier was not expecting a response but received one."
            )

        self.__awaiting_response = False  # Reset.

        if Q == 0:
            # Unpack arguments.
            ID = args

            # Check ID hashes.
            if tuple(map(sha256_hash, ID)) != self.__ID_hash:
                raise AuthenticationError("Invalid ID hashes.")

            # Check rank of S * M * T.
            if (ID[1] - ID[0]).rank() != self.__MR.r:
                raise AuthenticationError("Invalid rank.")
        elif Q == 1 or Q == 2:
            # Unpack arguments.
            (S, T, X) = args[0]
            beta = args[1]

            # Check nonsingularity of S and T.
            if not (S.is_invertible() and T.is_invertible()):
                raise AuthenticationError("S and T must be nonsingular.")

            # Check STX hash.
            if sha256_hash(args[0]) != self.__STX_hash:
                raise AuthenticationError("Invalid STX hash.")

            # Temporary linear combination with instance masked by S and T.
            temp = linear_combination(
                beta, [S * M * T for M in self.__MR.matrices]
            ) + X

            if Q == 1:
                if sha256_hash(temp) != self.__ID_hash[0]:
                    raise AuthenticationError("Invalid ID[0] hash.")
            else:
                if sha256_hash(temp - S * self.__MR.offset_matrix * T) != \
                       self.__ID_hash[1]:
                    raise AuthenticationError("Invalid ID[1] hash.")

    def __str__(self):
        """Pretty printing."""
        return "Verifier object.  Associated MR instance: " + \
            str(self.__MR) + "."


class MinRankInstance(object):
    """Represents an instance of the MinRank problem.

    Attributes:
        m: The size of the problem (m + 1 matrices in total).
        eta: The row dimension of each matrix.
        n: The column dimension of each matrix.
        r: The rank of the secret matrix.
        q: The size of the finite field in which arithmetic is
            performed.  Must be a prime number.
        matrices: The MR matrices (M_1, M_2, ..., M_m).
        offset_matrix: The base matrix (M_0).
        finite_field: GF(q).

    Methods:
        give_access: Gives access to the secret vector to a
            "legitimate prover".
    """
    def __init__(self, m, eta, n, r, q):
        """Initialize a MinRank instance object (a public/private key).

        Raises:
            AssertionError: Something went wrong with the computation.
        """
        # The finite field that will be used to perform arithmetic in.
        self.__finite_field = GF(q)

        # The eta x n matrix space in which the instance will be generated.
        self.__matrix_space = MatrixSpace(self.__finite_field, eta, n)

        # Generate all of the instance except for the very last matrix.
        self.__offset_matrix = self.__matrix_space.random_element()
        self.__Ms = [self.__matrix_space.random_element()
                     for _ in range(m - 1)]
        print("self.__Ms:", self.__Ms)


        # Generate the secret eta x n matrix M of rank r.
        self.__M = random_matrix(self.__finite_field,
                                 eta, n,
                                 algorithm='echelonizable', rank=r)
        self.__M.set_immutable()

        # Generate the secret vector alpha (last component must be non-zero).
        while True:
            self.__alpha = random_vector(self.__finite_field, m)
            if self.__alpha[-1] != 0:
                break

        # Deterministically generate the last part of the instance.
        self.__Ms.append(
            ((self.__M + self.__offset_matrix -
              linear_combination(self.__alpha[:-1], self.__Ms)) /
             self.__alpha[-1])
        )
        print("self.__Ms:", self.__Ms)


        # Assert that the instance was constructed well, i.e. the "secret
        # key" allows us to construct a matrix of rank r, namely M.
        assert (self.__M ==
                linear_combination(self.__alpha, self.__Ms) -
                self.__offset_matrix)

        # Make all matrices immutable and put them in a tuple rather than
        # a list.
        map(lambda M: M.set_immutable(), self.__Ms)
        self.__Ms = tuple(self.__Ms)

        # Store the parameters that were used.
        self.m = m
        self.eta = eta
        self.n = n
        self.r = r
        self.q = q

    @property
    def finite_field(self):
        """Returns the associated finite field."""
        return self.__finite_field

    @property
    def matrices(self):
        """Returns a tuple of the matrices associated to the instance."""
        return self.__Ms

    @property
    def offset_matrix(self):
        """Returns the offset matrix associated to the instance."""
        return self.__offset_matrix

    def give_access(self, legitimate_prover):
        """Gives access to the secret vector to a legitimate prover.

        Args:
            legitimate_prover: A LegitimateProver object (or descendant).

        Raises:
            TypeError: Not a valid LegitimateProver object.
        """
        if not isinstance(legitimate_prover, LegitimateProver):
            raise TypeError(
                "Attempted to give access to a prover who is not "
                "a LegitimateProver object."
            )

        legitimate_prover.alpha = deepcopy(self.__alpha)

    def __str__(self):
        """Pretty printing."""
        return "MR({:d}, {:d}, {:d}, {:d}, {:d})".format(
            self.m, self.eta, self.n, self.r, self.q
        )


def authentication_driver(prover, verifier, rounds=rounds):
    """Performs authentication."""
    for i in range(rounds):
        prover.prepare_round()
        prover.send_hashes(verifier)
        try:
            verifier.send_query(prover)
        except AuthenticationError as e:
            print(("Authentication unsucessful.\n"
                   "Failed at round: {:02d}\n"
                   "Reason         : {}").format(i + 1, str(e)))
            return False

    print("Authentication successful.")
    return True  # All checks passed.


#!/usr/bin/env sage -python
# -*- coding: utf-8 -*-

"""Sample tests for the MinRank implementation."""


__author__ = "Dario Gjorgjevski"
__email__ = "gjorgjevski.dario@students.finki.ukim.mk"
__license__ = "GPLv3"

# Seed for reproducibility.
set_random_seed(17)

#if __name__ == "__main__":
 #   # Parameters for challenge set A.
  #  m = 10
   # eta = 6
    #n = 6
#    r = 3
 #   q = 65521

  #  MR = MinRankInstance(m, eta, n, r, q)
   # print("Trying out authentication with challenge set A parameters.")

    #V = Verifier(MR)
#    P = Prover(MR)
 #   LP = LegitimateProver(MR)
  #  MR.give_access(LP)

   # print("Illegitimate prover goes first.")
    #authentication_driver(P, V)

#    print("Legitimate prover next.")
 #   authentication_driver(LP, V)

  #  # Small instance parameters.
   # m = 4
    #eta = n = 6
#    r = 3
 #   q = 7

  #  MR = MinRankInstance(m, eta, n, r, q)
   # A = MinRankAttack(MR)
    #print("Trying out the Groebner basis attack on a small instance that is guarenteed to have a solution.\n"
     #     "The y_i's are the solution.")
#    print(A.run_groebner())

    # print("Trying out the kernel attack on the same instance.")
    # print(A.run_kernel()) # Use the constrainted run instead

    # for D in range(2,10):
    #   print("Trying out the xl attack on the same instance.")
    #   print(A.run_xl(D))


class MinRankInstance(object):
    """Represents an instance of the MinRank problem initialized with UOV keys."""

    def __init__(self, m, eta, n, r, q):
        """Initialize a MinRank instance with random UOV keys (public key)."""
        # The finite field that will be used to perform arithmetic in.
        self.__finite_field = GF(q)

        # The eta x n matrix space in which the instance will be generated.
        self.__matrix_space = MatrixSpace(self.__finite_field, eta, n)

        P, F, T = self.generate_uov_keys(self.__finite_field, n, m)

        # Use UOV public keys for the matrices instead of generating them deterministically
        self.__Ms = [self.poly_to_matrix(f) for f in P]
        print(self.__Ms)
        # Generate a random offset matrix (similar to M_0 in the UOV signature scheme)
        self.__offset_matrix = self.__matrix_space.random_element()

        # Ensure that all matrices are immutable and stored as a tuple
        map(lambda M: M.set_immutable(), self.__Ms)
        self.__Ms = tuple(self.__Ms)

        # Store the parameters that were used
        self.m = m
        self.eta = eta
        self.n = n
        self.r = r
        self.q = q

    @property
    def finite_field(self):
        """Returns the associated finite field."""
        return self.__finite_field

    @property
    def matrices(self):
        """Returns a tuple of the matrices associated to the instance."""
        return self.__Ms

    @property
    def offset_matrix(self):
        """Returns the offset matrix associated to the instance."""
        return self.__offset_matrix

    def __str__(self):
        """Pretty printing."""
        return "MR(UOV keys with parameters m={:d}, eta={:d}, n={:d}, q={:d})".format(
            self.m, self.eta, self.n, self.q
        )


    def generate_uov_keys(self, k, n, m, order="deglex"):
        """Generate UOV keys using the provided parameters."""
        R = PolynomialRing(k, ["x%d" % i for i in range(1, n + 1)], order=order)
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

    def poly_to_matrix(self, f, symmetric=True):
        """Convert a quadratic polynomial to a matrix."""
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
        return Q


#!/usr/bin/env sage -python
# -*- coding: utf-8 -*-

"""Sample tests for the MinRank implementation."""


__author__ = "Dario Gjorgjevski"
__email__ = "gjorgjevski.dario@students.finki.ukim.mk"
__license__ = "GPLv3"

# Seed for reproducibility.
set_random_seed(17)

if __name__ == "__main__":
    # Parameters for challenge set A.
    # m = 10
    # eta = 6
    # n = 6
    # r = 3
    # q = 65521

    # MR = MinRankInstance(m, eta, n, r, q)
    # print("Trying out authentication with challenge set A parameters.")

    # V = Verifier(MR)
    # P = Prover(MR)
    # LP = LegitimateProver(MR)
    # MR.give_access(LP)

    # print("Illegitimate prover goes first.")
    # authentication_driver(P, V)

    # print("Legitimate prover next.")
    # authentication_driver(LP, V)

    # Small instance parameters.
    m = 7
    eta = n = 10
    r = 3
    q = 7

    print("hallo")
    MR = MinRankInstance(m, eta, n, r, q)
    A = MinRankAttack(MR)
    print("Trying out the Groebner basis attack on a small UOV instance.\n"
          "The y_i's are the solution.")
    print(A.run_groebner())

    # print("Trying out the kernel attack on the same instance.")
    # print(A.run_kernel()) # Use the constrainted run instead

    # for D in range(2,10):
    #   print("Trying out the xl attack on the same instance.")
    #   print(A.run_xl(D))


class MinRankInstance(object):
    """Represents an instance of the MinRank problem initialized with UOV keys."""

    def __init__(self, m, eta, n, r, q):
        """Initialize a MinRank instance with random UOV keys (public key)."""
        # The finite field that will be used to perform arithmetic in.
        self.__finite_field = GF(q)

        # The eta x n matrix space in which the instance will be generated.
        self.__matrix_space = MatrixSpace(self.__finite_field, eta, n)

        P, F, T = self.generate_keys_with_dependencies(self.__finite_field, n, m)

        # Use UOV public keys for the matrices instead of generating them deterministically
        self.__Ms = [self.poly_to_matrix(f) for f in P]

        # Generate a random offset matrix (similar to M_0 in the UOV signature scheme)
        self.__offset_matrix = self.__matrix_space.random_element()

        # Ensure that all matrices are immutable and stored as a tuple
        map(lambda M: M.set_immutable(), self.__Ms)
        self.__Ms = tuple(self.__Ms)

        # Store the parameters that were used
        self.m = m
        self.eta = eta
        self.n = n
        self.r = r
        self.q = q

    @property
    def finite_field(self):
        """Returns the associated finite field."""
        return self.__finite_field

    @property
    def matrices(self):
        """Returns a tuple of the matrices associated to the instance."""
        return self.__Ms

    @property
    def offset_matrix(self):
        """Returns the offset matrix associated to the instance."""
        return self.__offset_matrix

    def __str__(self):
        """Pretty printing."""
        return "MR(UOV keys with parameters m={:d}, eta={:d}, n={:d}, q={:d})".format(
            self.m, self.eta, self.n, self.q
        )



    def generate_random_list(self, ring, n):
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

    def generate_keys_with_dependencies(self, k, n, m, order="deglex"):
        R = PolynomialRing(k, ["x%d" % i for i in range(1,n+1)], order=order)
        M = MatrixSpace(k, n)
        L_list = self.generate_random_list(R, m)

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
        print(F)


        # Calculate the inverse of the coefficient of the first variable in L_list[0]
        # leading_coeff = L_list[0].coefficient(R.gens()[0])
        L_inv = 1 / L_list[0] # Calculate inverse of the coefficient
        F_1 = -L_list[1] * F[1]
        for i in range(2, m):
            F_1 -= L_list[i] * F[i]
        F_1 = L_inv*F_1
        F[0] = F_1  # Prepend F_1 to the list of polynomials F

        # Generate the secret transformation T.
        T = M.random_element()
        while not T.is_invertible():
            T = M.random_element()

        # Compose the central maps with T.
        P = [T.act_on_polynomial(f) for f in F]
        return P, F, T


    def poly_to_matrix(self, f, symmetric=True):
        """Convert a quadratic polynomial to a matrix."""
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
        return Q


#!/usr/bin/env sage -python
# -*- coding: utf-8 -*-

"""Sample tests for the MinRank implementation."""


__author__ = "Dario Gjorgjevski"
__email__ = "gjorgjevski.dario@students.finki.ukim.mk"
__license__ = "GPLv3"

# Seed for reproducibility.
set_random_seed(17)

if __name__ == "__main__":
    # Parameters for challenge set A.
    # m = 10
    # eta = 6
    # n = 6
    # r = 3
    # q = 65521

    # MR = MinRankInstance(m, eta, n, r, q)
    # print("Trying out authentication with challenge set A parameters.")

    # V = Verifier(MR)
    # P = Prover(MR)
    # LP = LegitimateProver(MR)
    # MR.give_access(LP)

    # print("Illegitimate prover goes first.")
    # authentication_driver(P, V)

    # print("Legitimate prover next.")
    # authentication_driver(LP, V)

    # Small instance parameters.
    # m = 2
    # eta = n = 5
    # r = 3
    # q = 2

    print("hallo")
    MR = MinRankInstance(m, eta, n, r, q)
    A = MinRankAttack(MR)
    print("Trying out the Groebner basis attack on a small UOV instance that contains a linear dependency.\n"
          "The y_i's are the solution.")
    print(A.run_groebner())

    # print("Trying out the kernel attack on the same instance.")
    # print(A.run_kernel()) # Use the constrainted run instead

    # for D in range(2,10):
    #   print("Trying out the xl attack on the same instance.")
    #   print(A.run_xl(D))

