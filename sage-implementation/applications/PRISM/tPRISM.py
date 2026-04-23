from sage.all import *
from sage.algebras.quatalg.quaternion_algebra import *
import random

import sys
sys.path.insert(0, '../..')
sys.path.insert(0, '../../ideal_to_isogeny')

from ideal_to_isogeny.endomorphisms import FullrepresentInteger, iota, pi
from quaternions.ideals import is_cyclic, random_equivalent_ideal, reduced_basis, make_cyclic, quadratic_norm, chi, ideal_generator, small_equivalent_ideal, pullback_ideal
from quaternions.lattices import generate_close_vectors
from utilities.sum_of_squares import sum_of_squares
from qlapoti23 import qlapoti23
from ideal_to_isogeny.ideal_to_isogeny_qlapoti23 import IdealToIsogenyQlapotis23
from ideal_to_isogeny.quaternion_helpers.helpers import reduced_ideal
from precomputations_PRSIM import Precomputations_PRISM
from others.utilities.discrete_log import BiDLP
from others.montgomery_isogenies.kummer_isogeny import KummerLineIsogeny
from montgomery_isogenies.kummer_line import KummerLine


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

def strong_approximation_construct_lattice(N, C, D, λ, L, small_power_of_two=False):
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


def strong_approximation_lattice_heuristic(N, C, D, λ, L, small_power_of_two=False):
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
        N, C, D, λ, L, small_power_of_two=small_power_of_two
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

    μ = N * xp + N * yp * QA_i + (λ * C + N * zp) * QA_j + (λ * D + N * tp) * QA_j * QA_i

    # Check that Nrd(μ) == L
    # and that μ is in O0
    assert μ.reduced_norm() == L
    assert μ in O0
    return μ

def StrongApproximationHeuristic(
    N, C, D, facT, composite_factors=None, small_power_of_two=False
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
    for _ in range(100):
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
            N, C, D, λ, L2, small_power_of_two=small_power_of_two
        )
        # Sometimes we have no valid solutions from the lattice,
        # so we try again with a new L2.
        if μ:
            return μ
    # All attempts for L2 failed. Pick a new N by regenerating γ
    return None

def IdealToIsogeny3b(I, precomps):
    α = ideal_generator(I)
    nI = I.norm()
    assert 3**b % nI == 0
    denom = α.denominator()
    mod_denom = inverse_mod(denom, nI)
    R, S = precomps.basis3
    R, S = (3**b / nI) * R, (3**b / nI) * S
    tmpR = (α[0] * denom) * R
    tmpR = tmpR + (α[1] * denom) * iota(R)
    tmpR = tmpR + (α[2] * denom) * pi(R)
    tmpR = tmpR + (α[3] * denom) * iota(pi(R))

    tmpS = (α[0] * denom) * S
    tmpS = tmpS + (α[1] * denom) * iota(S)
    tmpS = tmpS + (α[2] * denom) * pi(S)
    tmpS = tmpS + (α[3] * denom) * iota(pi(S))

    tmpR, tmpS = mod_denom * tmpR, mod_denom * tmpS

    if tmpR.is_zero(): return R
    if tmpS.is_zero(): return S
    x = None
    if not (3**(b-1) * tmpS).is_zero():
        x = tmpS.discrete_log(tmpR)
    else:
        x = tmpR.discrete_log(tmpS)
        return S - x*R
    return R - x*S

# Input I of norm < p^{1/4} and t >= 5
# Output an equivalent ideal J ~ I such that n(J) = 3^{bt}
def KLPT_threshold(I, t):
    max_attemps = 10
    gap = 2
    for _ in range(max_attemps):
        γ = FullrepresentInteger(q1 * 3**(2*b), prime, primitive=True)
        γ = γ[0] + γ[1] * QA_i + γ[2] * QA_j + γ[3] * QA_k
        C0, D0 = IdealModConstraint(I, γ)
        v = StrongApproximationHeuristic(q1, C0, D0, factor(3**(b*t + gap - 2*b)))
        if v:
            beta = γ * v
            J = chi(beta, I)
            assert(I.is_left_equivalent(J))
            return J
    return None

# J must be a cyclic 3^{bt}-isogeny
def LongIdealToIsogeny(J, precomps):
    if not isinstance(precomps, Precomputations_PRISM):
        raise TypeError("Functions assumes that the input is of type `Precomputations_PRISM`")
    
    ϕ_list = []
    m = J.norm().valuation(3)
    t = m // b

    # IdealtoIsogeny for ideals of norm 3^b
    J1 = J + O0 * 3**b
    assert is_cyclic(J1), "J1 is not cyclic"
    assert 3**b % J1.norm() == 0, "J1.norm is {0}".format(J1.norm().factor())

    J1ker = IdealToIsogeny3b(J1, precomps)
    _E0 = KummerLine(E0)
    _J1ker = _E0(J1ker[0])
    ϕ1 = KummerLineIsogeny(_E0, _J1ker, J1.norm())
    ϕ_list.append(ϕ1)

    J_prev = J1
    prev_steps = J1.norm().valuation(3)

    while prev_steps < m:
        assert is_cyclic(J_prev)
        J_prev_red = reduced_ideal(J_prev.conjugate()).conjugate()
        print("J_prev_red norm", J_prev_red.norm())
        while True:
            K, _, _ = random_equivalent_ideal(J_prev_red, adjust_right_order=True)
            if K.norm() % 3 != 0: break
        assert K.is_right_equivalent(J_prev)
        print(f'K norm : {K.norm()}')
        # K = small_equivalent_ideal(J1)
        Jilong = (J_prev.conjugate() * J).scale(1/J_prev.norm())

        Ji = pullback_ideal(Jilong, K)
        Oi = Ji.left_order()
        beta = Oi.isomorphism_to(O0, conjugator=True)
        K = beta**(-1) * K * beta
        Ji = beta**(-1) * Ji * beta
        assert Ji.left_order() == O0
        assert K.left_order() == O0
        Ji = Ji + O0 * 3**b
        assert is_cyclic(Ji), "Ji is not cyclic"
        assert 3**b % Ji.norm() == 0, "Ji.norm is {0}".format(Ji.norm())
        prev_steps += Ji.norm().valuation(3)

        Jiker = IdealToIsogeny3b(Ji, precomps)

        phi_aux = IdealToIsogenyQlapotis23(K, a, b, precomps)
        P, Q = precomps.basis23
        P, Q = 2**a * P, 2**a * Q
        x, y = BiDLP(Jiker, P, Q, 3**b)
        imE, imP, imQ = phi_aux.images()
        imJiker = 2**a * (x * imP + y * imQ)
        assert imJiker.order() == 3**b
        _imE = KummerLine(imE)
        _imJiker = _imE(imJiker[0])
        ϕi = KummerLineIsogeny(_imE, _imJiker, Ji.norm())
        ϕ_list.append(ϕi)
        J_prev = J_prev * (Jilong + Jilong.left_order() * 3**b)
        print('prev_steps:', prev_steps)

    return ϕ_list

# Global parameter settings
prime = 0x70132bcd7e31e9dc896d5b63af3550280be9f5e2e89fb82b9f0bd81a4a28961b51ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
F = GF(prime**2, name="i", modulus=[1, 0, 1])
E0 = EllipticCurve(F, [1, 0])
E0.set_order((prime + 1)**2)
ell = 3
a = 256
b = 162
t = 5
QA = QuaternionAlgebra(-1, -prime)
QA_i, QA_j, QA_k = QA.gens()
O0 = QA.quaternion_order([1, QA_i, QA_i/2 + QA_j/2, QA_k/2 + QA(1)/2])
sqrt_prime = ceil(sqrt(prime))

# Choose random ideal
q1, q2 = random_prime(ceil(prime**(1/8))), random_prime(prime)
# print(q1, q2)
# print(q1 * q2 > prime)
alpha = FullrepresentInteger(q1 * q2, prime)
I = O0 * alpha + O0 * q1
assert(I.norm() == q1)

equiv_ideals = []
equiv_ideals.append(KLPT_threshold(I, t))
precomps = Precomputations_PRISM(prime, 122, a = a, b = b, role='threshold')
assert len(equiv_ideals) != 0
J, _ = make_cyclic(equiv_ideals[0])
ϕ_J = LongIdealToIsogeny(J, precomps)