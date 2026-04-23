"""

WARNING WARNING WARNING WARNING WARNING WARNING WARNING WARNING WARNING WARNING WARNING

THIS FILE WILL NOT WORK PROPERLY AS THE OLD KLPT LIKE CODE HAD A BUNCH OF
GLOBALS BECAUSE PAST JACK MADE VERY BAD CODING DECISIONS BUT IT SHOULD BE ABLE
TO B FIXED WITH SMALL CHANGES

WARNING WARNING WARNING WARNING WARNING WARNING WARNING WARNING WARNING WARNING WARNING

"""


# Python imports
from random import choice

# Sage imports
from sage.all import gcd, ZZ, floor, sqrt, randint, kronecker, random_prime
from sage.all import QuaternionAlgebra, CRT, vector, inverse_mod, ceil, prod, Zmod, Matrix, flatten

# Local imports
from quaternions.ideals import (
    chi,
    reduced_basis,
    quadratic_norm,
)
from utilities.sum_of_squares import sum_of_squares
from quaternions.lattices import generate_small_norm_quat, generate_close_vectors


def is_inert(ω, p):
    """
    Given an element ω ∈ B, and a prime p, returns if
    p is inert in ℤ[ω]

    For ℤ[ω], a prime is inert when the Kronecker symbol:
        (-d / p) = -1
    """

    def discriminant(ω):
        """
        Computes the discriminant of an element of a
        quaternion algebra, denoted Δ(ω)
        """
        Trd = ω.reduced_trace()
        Nrd = ω.reduced_norm()
        if Trd not in ZZ or Nrd not in ZZ:
            raise ValueError(f"The element ω must be integral")

        return ZZ(Trd**2 - 4 * Nrd)

    def recover_d(ω):
        """
        Given an integral element of a Quaternion Algebra,
        and its discriminant Δ(ω), computes the integer d
        such that:

        Δ(ω) = -d    if d ≡ 3 mod 4
             = -4d   otherwise
        """
        Δ = discriminant(ω)
        if Δ % 4 == 0:
            return -(Δ // 4)
        return -Δ

    d = recover_d(ω)
    return kronecker(-d, p) == -1


def inert_prime(bound, d):
    """
    Input: An upper bound for the output prime
           d, the integer such that ω^2 = -d for
           ℤ[ω]

    Output: A prime < bound which is inert in
            the ring ℤ[ω]
    """
    while True:
        p = random_prime(bound)
        if kronecker(-d, p) == -1:
            return p


def generate_small_norm_quat_random(Ibasis, coeff_bound, search_bound):
    """
    Pick a random linear combination from Ibasis to compute an element
    α ∈ B_{0, ∞}
    """
    for _ in range(search_bound):
        xs = [randint(-coeff_bound, coeff_bound) for _ in range(len(Ibasis))]
        if gcd(xs) != 1:
            continue
        α = sum(αi * x for αi, x in zip(Ibasis, xs))

        yield α


# TODO: prime_norm_heuristic should be derived, before it was a global
def prime_norm_algebra_element(
    nI,
    Ibasis,
    coeff_bound,
    search_bound,
    previous=set(),
    allowed_factors=None,
    random_elements=False,
    prime_norm_heuristic=200,  # TODO this should be set as we do in SQISign-SageMath
):
    """
    Find an element α ∈ B_{0, ∞} with small,
    prime scaled norm.

    Optional: `allowed_factors` allows the norm to
               be composite, where it is expected that
               the result is a large prime multiplied by
               small factors dividing allowed_factors.
    """

    if random_elements:
        small_elements = generate_small_norm_quat_random(
            Ibasis, coeff_bound, search_bound
        )
    else:
        max_norm_bound = prime_norm_heuristic
        small_elements = generate_small_norm_quat(
            Ibasis, max_norm_bound, count=search_bound
        )

    for α in small_elements:
        α_norm = ZZ(α.reduced_norm()) // nI

        # Even norms can be rejected early
        # as allowed_factors is either odd
        # or None.
        if α_norm % 2 == 0:
            continue

        # We can allow α to have composite norm
        # if small factors are within the KLPT
        # target norm T.
        α_norm_reduced = α_norm
        if allowed_factors:
            g = gcd(α_norm, allowed_factors)
            if g != 1:
                α_norm_reduced //= g

        # If we've failed with this norm before
        # continue
        if α_norm_reduced in previous:
            continue

        # Check if the element has prime norm
        if α_norm_reduced.is_pseudoprime():
            # Check if the prime small enough
            if α_norm_reduced < prime_norm_heuristic:
                return α, α_norm
    return None, None


# TODO: logp should be derived, before it was a global
def EquivalentPrimeIdealHeuristic(
    I, previous=set(), allowed_factors=None, random_elements=False, logp=256
):
    """
    Given an ideal I with norm nI, attempts
    to find an equivalent ideal J with prime norm.

    If unsuccessful, returns None
    """
    # TODO: what's a good initial small search?
    coeff_bound = max((floor(logp / 10)), 7)

    # TODO: what's a good search bound?
    search_bound = max(coeff_bound**4, 4096)

    # Norm of Ideal
    nI = ZZ(I.norm())

    # Compute the Minkowski reduced basis
    Ibasis = reduced_basis(I)

    # Find an element with small prime norm
    α, N = prime_norm_algebra_element(
        nI,
        Ibasis,
        coeff_bound,
        search_bound,
        previous=previous,
        allowed_factors=allowed_factors,
        random_elements=random_elements,
    )

    if α is None:
        print(f"DEBUG [EquivalentPrimeIdealHeuristic] No equivalent prime found")
        return None, None, None

    assert ZZ(α.reduced_norm()) // nI == N
    assert α in I

    # Compute the ideal given α
    J = chi(α, I)

    return J, N, α


def RepresentIntegerHeuristic(M, parity=False):
    """
    Algorithm 1 (Page 8)

    Given an integer M, with M > p, attempts to
    find a random element γ with norm M.

    If no element is found after `bound` tries,
    returns none
    """

    def RepresentInteger(M, z, t, parity=False):
        M_prime = M - p * quadratic_norm(z, t)
        two_squares = sum_of_squares(M_prime)
        if two_squares:
            x, y = two_squares
            if parity and (x + t) % 2 == 0 and (y + z) % 2 == 0:
                return None
            return x + ω * y + j * (z + ω * t)
        # No solution for the given M
        return None

    if M <= p:
        raise ValueError(f"Can only represent integers M > p.")
    m = max(floor(sqrt(M / (p * (1 + q)))), 5)

    # TODO: how many times should we try?
    for _ in range(m**2):
        z = randint(-m, m)
        t = randint(-m, m)
        γ = RepresentInteger(M, z, t, parity=parity)

        if γ is not None:
            # Found a valid solution, return
            assert γ.reduced_norm() == M, "The norm is incorrect"
            assert γ in O0, "The element is not contained in O0"
            return γ

    # No solution found, return None
    print(f"DEBUG [RepresentIntegerHeuristic]: No solution found")
    return None


def EquivalentRandomEichlerIdeal(I, Nτ):
    """
    Algorithm 6 (SQISign paper)

    Input:  I a left O-ideal
    Output: K ∼ I of norm coprime with Nτ
    """
    nI = I.norm()
    # TODO: what should the size of `bound` be
    bound = 10

    # Step 1: find an element ωS such that Nτ is inert in ℤ[ωS]
    O = I.left_order()
    while True:
        ωS = sum([randint(-bound, bound) * b for b in O.basis()])
        if is_inert(ωS, Nτ):
            break

    # Step 2: find a random element γ in I such that n(γ)/n(I) is coprime with Nτ
    while True:
        γ = sum([randint(-bound, bound) * b for b in I.basis()])
        if gcd(γ.reduced_norm() // nI, Nτ) == 1:
            break

    # Step 3: select a random class (C : D) ∈ P1(Z/Nτ Z).
    x = randint(0, Nτ)
    if x == p:
        C, D = 1, 0
    else:
        C, D = x, 1

    # Step 4: set β = (C + ωSD)γ.
    β = (C + ωS * D) * γ

    # Step 5: return K = χI(β)
    return chi(β, I)

def solve_mod_constraint_kernel(quat_list):
    """
    Helper function which given a list of 8 quaternions
    constructs a matrix and computes its kernel.

    Used in `IdealModConstraint` and `EichlerModConstraint`
    to compute C, D.
    """
    # Split each element of B into its coefficients
    # a ∈ B = t + x i + y j + z k: t,x,y,x ∈ Q
    matrix_coefficients = flatten([x.coefficient_tuple() for x in quat_list])

    # We now have 32 elements, four coefficients from each
    # element
    assert len(matrix_coefficients) == 8 * 4

    # Create an 8x4 matrix over QQ from the coefficients
    mat = Matrix(8, 4, matrix_coefficients)

    # Clear the denominator and work over ZZ
    mat, _ = mat._clear_denom()

    # Compute its kernel
    kernel = mat.kernel()

    # Following the SQISign MAGMA code, we pick
    # the third row.
    row = kernel.basis()[2]
    C, D = row[2:4]  # row = A,B,C,D,_,_,_,_

    return C, D

def IdealModConstraint(I, γ):
    """
    Section 4.3

    Given an ideal I of norm N and an element
    γ of a maximal order O0 of norm NM finds
    (C0 : D0) in P^1(Z/NZ) such that

    μ0 = j(C0 + ωD0)

    Then verifies that γ*μ0 in I
    """
    QA_i, QA_j, _ = I.quaternion_algebra().gens()
    ω = QA_i
    N = I.norm()
    # First four elements constructed from γ
    matrix_quaternions = [γ * N, γ * N * ω, γ * QA_j, γ * QA_j * ω]

    # Next four elements are the basis of the ideal I
    matrix_quaternions += list(I.basis())

    # We should now have a list of 8 elements of B
    assert len(matrix_quaternions) == 8

    # Generate a 8x4 matrix matrix from these quaternions
    C0, D0 = solve_mod_constraint_kernel(matrix_quaternions)
    μ0 = QA_j * (C0 + ω * D0)

    # Check we made it correctly
    assert γ * μ0 in I

    if C0 == 0 or D0 == 0:
        print(f"DEBUG [IdealModConstraint]: Something is maybe going to break...")
        print(f"{C0 = }")
        print(f"{D0 = }")
    return C0, D0


def generate_bounded_divisor(bound, T, facT):
    """
    Finds L2 > bound powersmooth
    We want the result to divide T
    """
    L2, facL2 = 1, dict()

    # Compute a random factor L2 | T
    # and create dict to keep track 
    # of exp.
    for pi, ei in facT:
        exp = ei - randint(0, ei)
        L2 *= pi**exp
        facL2[pi] = exp

    # Mul random factors from T until L2 
    # is large enough
    while L2 <= bound:
        pi, ei = choice(facT)
        if facL2[pi] < ei:
            L2 *= pi
            facL2[pi] += 1

    return ZZ(L2)

def strong_approximation_construct_lattice(prime, N, C, D, λ, L, small_power_of_two=False):
    """
    Constructing the lattice basis and target vector following PS18

    When N is a power of two, we have `small_power_of_two`
    set to True. When this is the case we double the
    modulus and halve coeff_z, coeff_t
    """

    if small_power_of_two:
        coeff_z = prime * λ * C
        coeff_t = prime * λ * D
    else:
        coeff_z = 2 * prime * λ * C
        coeff_t = 2 * prime * λ * D

    cst_term = L - prime * λ**2 * quadratic_norm(C, D)

    if small_power_of_two:
        cst_term, check = cst_term.quo_rem(2 * N)
    else:
        cst_term, check = cst_term.quo_rem(N)
    assert check == 0

    coeff_t_inv = inverse_mod(coeff_t, N)

    zp0 = 0
    tp0 = ZZ(cst_term * coeff_t_inv % N)

    # Construct the lattice basis
    lattice_basis = N * Matrix(ZZ, [[1, ZZ((-coeff_z * coeff_t_inv) % N)], [0, N]])

    # Construct the target vector
    target = λ * vector([ZZ(C), ZZ(D)]) + N * vector([zp0, tp0])
    return lattice_basis, target, zp0, tp0


def strong_approximation_lattice_heuristic(prime, N, C, D, λ, L, small_power_of_two=False):
    """
    Constructs a lattice basis and then looks for
    close vectors to the target.

    Allows for optimising output from pN^4 to pN^3,
    which helps keep the norm small and hence the
    degree of the isogenies small
    """

    # We really only expect this for the case when N = 2^k
    swap = False
    if D == 0 or gcd(D, N) != 1:
        C, D = D, C
        swap = True

    # Construct the lattice
    lattice_basis, target, zp0, tp0 = strong_approximation_construct_lattice(
        prime, N, C, D, λ, L, small_power_of_two=small_power_of_two
    )

    # Generate vectors close to target
    close_vectors = generate_close_vectors(lattice_basis, -target, prime, L)

    xp, yp = None, None
    for close_v in close_vectors:
        zp, tp = close_v
        assert zp % N == 0, "Can't divide zp by N"
        assert tp % N == 0, "Can't divide tp by N"

        zp = ZZ(zp / N) + zp0
        tp = ZZ(tp / N) + tp0
        M = L - prime * quadratic_norm(λ * C + zp * N, λ * D + tp * N)
        M, check = M.quo_rem(N**2)
        assert check == 0, "Cant divide by N^2"

        if M < 0:
            continue

        # Try and find a solution to
        # M = x^2 + y^2
        two_squares = sum_of_squares(ZZ(M))
        if two_squares != []:
            xp, yp = two_squares[0], two_squares[1]
            break

    if xp is None:
        # Never found vector which had a valid solution
        return None

    # Use solution to construct element μ
    # μ = λ*j*(C + D*ω) + N*(xp + ω*yp + j*(zp + ω*tp))

    # If we swapped earlier, swap again!
    if swap:
        C, D = D, C
        tp, zp = zp, tp
    QA = QuaternionAlgebra(-1, -prime)
    QA_i, QA_j, QA_k = QA.gens()
    O0 = QA.quaternion_order([1, QA_i, QA_i/2 + QA_j/2, QA_k/2 + QA(1)/2])
    μ = N * xp + N * yp * QA_i + (λ * C + N * zp) * QA_j + (λ * D + N * tp) * QA_j * QA_i

    # Check that Nrd(μ) == L
    # and that μ is in O0
    assert μ.reduced_norm() == L
    assert μ in O0
    return μ

def StrongApproximationHeuristic(
    prime, N, C, D, facT, composite_factors=None, small_power_of_two=False
):
    """
    Algorithm 2 (Page 9)

    Given an N such and two integers C, D such that
    μ0 = j(C + ωD), we find a
      μ = λμ0 + N μ1
    such that the norm of μ is a divisor of facT

    This function works when:
    - Case 1: When N is prime
    - Case 2: When N is a power of two
    - Case 3: When N is composite.

    For Case 2, the optional bool small_power_of_two must be True
    For Case 3, the factors of N must be included in the
    optional argument: composite_factors
    """

    # For Case 2
    if small_power_of_two:
        # When we work with N = 2^k, we
        # work mod 2N and halve the lattice
        K = Zmod(2 * N)

    # For Case 1 and Case 3
    else:
        K = Zmod(N)

    # Check whether T is large enough to find
    # solutions
    T = prod([l**e for l, e in facT])
    # Case 3: N = N1*N2
    # For the case in SigningKLPT when N is the product of two
    # primes, we have a fixed L2. So, we try this and return
    # None if it fails
    if composite_factors:
        NL, Nτ = composite_factors
        assert NL * Nτ == N, "Supplied factors are incorrect"

        # Bound is fixed
        L2 = T

        # Make sure we can compute λ^2
        try:
            λλ = K(L2) / K(prime * quadratic_norm(C, D))
        except Exception as e:
            # p*(C^2 + D^2) is not invertible mod N
            print(f"ERROR [StrongApproximationHeuristic]: {e}")
            return None

        # Recover the square root with CRT
        # We supply C, D such that we can take the sqrt
        # no need to check this is possible
        λL = ZZ(Zmod(NL)(λλ).sqrt())
        λτ = ZZ(Zmod(Nτ)(λλ).sqrt())
        λ = CRT([λL, λτ], [NL, Nτ])

        # Not sure why, but this sometimes happens...
        if λ == 0:
            return None

        # If the lattice computation fails this returns None
        return strong_approximation_lattice_heuristic(
            N, C, D, λ, L2, small_power_of_two=small_power_of_two
        )

    # Case 1: N is prime
    # Case 2: N = l^2
    # Otherwise, we can pick a bunch of L2 and check if
    # any of them work.
    tested = set()

    # Debugging make sure the bound is ok for given T
    bound = ceil((prime * N**3))
    if bound > T:
        print(
            f"DEBUG [StrongApproximationHeuristic] The prime norm is too large, "
            f"no valid divisors. N ~ 2^{N.nbits()}, T ~ 2^{T.nbits()}"
        )
        return None

    L2 = T * 3
    # Try and find μ by testing a bunch of different L2 | T
    for _ in range(1):
        # L2 = generate_bounded_divisor(bound, T, facT)
        # if L2 in tested:
        #     continue
        # tested.add(L2)
        L2 /= 3

        # Check given L2 whether we can compute λ
        try:
            λλ = K(L2) / K(prime * quadratic_norm(C, D))
        except:
            # p*(C^2 + D^2) is not invertible mod N
            # Not sure why this is happening...
            return None

        # Ensure we can compute λ from λ^2
        if not λλ.is_square():
            continue

        λ = ZZ(λλ.sqrt())

        # Not sure why, but this sometimes happens...
        if λ == 0:
            continue

        μ = strong_approximation_lattice_heuristic(
            prime, N, C, D, λ, L2, small_power_of_two=small_power_of_two
        )
        # Sometimes we have no valid solutions from the lattice,
        # so we try again with a new L2.
        if μ:
            return μ
    # All attempts for L2 failed. Pick a new N by regenerating γ
    return None