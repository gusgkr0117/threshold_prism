from sage.all import *
from sage.algebras.quatalg.quaternion_algebra import *
import random
import json, math
from itertools import combinations
import hashlib

import sys
sys.path.insert(0, '../..')
sys.path.insert(0, '../../ideal_to_isogeny')

import params
from ideal_to_isogeny.endomorphisms import FullrepresentInteger, iota, pi
from quaternions.ideals import is_cyclic, random_equivalent_ideal, make_cyclic, chi, ideal_generator, small_equivalent_ideal, pullback_ideal
from PRISM.quaternions.klpt import IdealModConstraint, StrongApproximationHeuristic
from ideal_to_isogeny.ideal_to_isogeny_qlapoti import IdealToIsogenyQlapotis
from ideal_to_isogeny.ideal_to_isogeny_qlapoti23 import IdealToIsogenyQlapotis23
from ideal_to_isogeny.quaternion_helpers.helpers import reduced_ideal
from ideal_to_isogeny.dim2_wrapper import Dim2Isogeny
from precomputations_PRSIM import Precomputations_PRISM
from PRISM.utilities.supersingular import torsion_basis_with_pairing_2e
from others.utilities.discrete_log import BiDLP, discrete_log_pari
from others.montgomery_isogenies.kummer_isogeny import KummerLineIsogeny
from montgomery_isogenies.kummer_line import KummerLine

def random_function(n, t):
    x = [-1]
    for _ in range(n):
        x.append(random.randint(1, t))
    return x

def HashToPrime(msg, pk_curve, counter=0, level=1):
    """
    Hash (message || pk || counter) into a a-1 bit number
    increasing counter until the output is prime.
    Level is the security level
    """
    msg += str(pk_curve.j_invariant()).encode()

    while True:
        if level == 1:
            h = hashlib.sha256(msg + str(counter).encode()).digest()
        elif level == 3:
            h = hashlib.sha384(msg + str(counter).encode()).digest()
        else:
            h = hashlib.sha512(msg + str(counter).encode()).digest()

        exp2 = params.levels_threshold[level]['a']
        q = int.from_bytes(h, 'big') % 2**(exp2 - 2)
        if is_pseudoprime(q) and (2**(exp2-2) - q) % 3 != 0:
            return q, counter
        counter += 1

class threshold_PRISM_sign:
    def __init__(self, t, n, precomps = None, level = 1):
        prime = params.levels_threshold[level]['p']
        a = params.levels_threshold[level]['a']
        b = params.levels_threshold[level]['b']
        self.t = t
        self.n = n
        self.level = level
        self.security_param = {1:128, 3:192, 5:256}[level]
        if not precomps:
            precomps = Precomputations_PRISM(prime, 122, a = a, b = b, role='threshold')
        self.precomps = precomps

    def GenHashFamily(self):
        n, t = self.n, self.t
        n_list = list(range(1, n+1))
        t_set = set(range(1, t+1))
        h_list = []
        obtained_subsets = []

        while True:
            h = random_function(n, t)
            is_new = False
            for subset in combinations(n_list, t):
                if set(subset) in obtained_subsets: continue
                im_subset = [h[x] for x in subset]
                if set(im_subset)==set(t_set):
                    obtained_subsets.append(set(subset))
                    is_new = True
            if is_new : h_list.append(h)
            if len(obtained_subsets) == math.comb(n, t): break

        return h_list, len(h_list)
    
    def SelectHashFunc(self, h_list, subset):
        assert set(subset).issubset(range(1, self.n + 1))
        for i in range(len(h_list)):
            h = h_list[i]
            im_subset = [h[x] for x in subset]
            if set(im_subset) == set(range(1, self.t + 1)):
                return i
        return None

    def IdealToIsogeny3b(self, I):
        b = self.precomps.b
        α = ideal_generator(I)
        nI = I.norm()
        assert 3**b % nI == 0
        denom = α.denominator()
        mod_denom = inverse_mod(denom, nI)
        R, S = self.precomps.basis3
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
        if not ((nI / 3) * tmpS).is_zero():
            x = tmpS.discrete_log(tmpR)
        else:
            x = tmpR.discrete_log(tmpS)
            return S - x*R
        return R - x*S

    # Input I of norm < p^{1/4} and t >= 5
    # Output an equivalent ideal J ~ I such that n(J) = 3^{bt}
    def KLPT_threshold(self, I, m):
        max_attemps = 10
        prime = self.precomps.p
        q1 = Integer(I.norm())
        e = ceil(log(prime / q1, 3)) + 5

        QA_i, QA_j, QA_k = self.precomps.B.gens()
        for _ in range(max_attemps):
            γ = FullrepresentInteger(q1 * 3**e, prime, primitive=True)
            γ = γ[0] + γ[1] * QA_i + γ[2] * QA_j + γ[3] * QA_k
            C0, D0 = IdealModConstraint(I, γ)
            v = StrongApproximationHeuristic(prime, q1, C0, D0, factor(3**(m - e)))
            if v:
                beta = γ * v
                J = chi(beta, I)
                if not is_cyclic(J): continue
                assert(I.is_left_equivalent(J))
                return J
        return None

    # J must be a cyclic 3^{bt}-isogeny
    def LongIdealToIsogeny(self, J, v):
        b = self.precomps.b
        a = self.precomps.a
        O0 = self.precomps.O0
        E0 = self.precomps.E0

        nJ = J.norm()
        m = nJ.valuation(3)
        assert m % v == 0 and is_cyclic(J) and v >= b

        ϕ_list = []

        # IdealtoIsogeny for ideals of norm 3^b
        J1 = J + O0 * 3**b
        nJ1 = J1.norm()
        assert is_cyclic(J1), "J1 is not cyclic"
        assert 3**b % nJ1 == 0, "J1.norm is {0}".format(nJ1.factor())

        J1ker = self.IdealToIsogeny3b(J1)
        _E0 = KummerLine(E0)
        _J1ker = _E0(J1ker[0])
        ϕ1 = KummerLineIsogeny(_E0, _J1ker, nJ1)
        ϕ_fragment = [ϕ1]
        if v == b :
            ϕ_list.append(ϕ1)
            ϕ_fragment = []

        J_prev = J1
        prev_steps = nJ1.valuation(3)
        prev_v = prev_steps % v

        while prev_steps < m:
            # Compute an equivalent ideal K ~ J_1 * ... * J_(i-1)
            J_prev_red = reduced_ideal(J_prev.conjugate()).conjugate()
            while True:
                K, _, _ = random_equivalent_ideal(J_prev_red, adjust_right_order=True)
                if K.norm() % 3 != 0: break
            assert K.is_right_equivalent(J_prev)
            # print(f'K norm : {K.norm()}')
            # K = small_equivalent_ideal(J1)
            Jilong = (J_prev.conjugate() * J).scale(1/J_prev.norm())

            # Compute the pullback of i-th ideal J_i, i.e. [J_prev]^*J_i
            Ji = pullback_ideal(Jilong, K)
            Oi = Ji.left_order()
            beta = Oi.isomorphism_to(O0, conjugator=True)
            K = beta**(-1) * K * beta
            Ji = beta**(-1) * Ji * beta
            assert Ji.left_order() == O0
            assert K.left_order() == O0

            Jilen = min(v - prev_v, b)
            Ji = Ji + O0 * (3**Jilen)
            nJi = Ji.norm()
            Jilen = nJi.valuation(3)
            assert is_cyclic(Ji), "Ji is not cyclic"
            assert prev_v + Jilen <= v, "Ji.norm is {0}".format(nJi)
            prev_steps += Jilen
            prev_v = (prev_v + Jilen) % v

            # Compute the kernel of [J_prev]^*J_i
            Jiker = self.IdealToIsogeny3b(Ji)

            # phi_aux <- IdealToIsogeny(K)
            phi_aux = IdealToIsogenyQlapotis23(K, a, b, self.precomps, allow_diags=False)

            # Compute ker phi_i = phi_aux(ker([J_prev]^*J_i))
            P, Q = self.precomps.basis23
            cofactor = (2**a * 3**b) / nJi
            P, Q = cofactor * P, cofactor * Q
            x, y = BiDLP(Jiker, P, Q, nJi)
            imE, imP, imQ = phi_aux.images()
            imJiker = cofactor * (x * imP + y * imQ)
            assert imJiker.order() == nJi
            _imE = KummerLine(imE)
            _imJiker = _imE(imJiker[0])
            ϕi = KummerLineIsogeny(_imE, _imJiker, nJi)
            ϕ_fragment.append(ϕi)
            if prev_v == 0:
                ϕ_list.append(ϕ_fragment)
                ϕ_fragment = []
            J_prev = J_prev * (Jilong + Jilong.left_order() * nJi)

        return ϕ_list
    
    def keygen(self, precomp_file = None, backup_file = None):
        if precomp_file:
            f = open(precomp_file, 'r')
            json_data = json.load(f)
            h_list = json_data['h_list']
            h_len = len(h_list)
            isog_paths = json_data['isog_paths']
            isog_paths = [[[KummerLineIsogeny.from_list(isog_frag, self.precomps) for isog_frag in isog] for isog in isog_path] for isog_path in isog_paths]
            f.close()
        else:
            p = self.precomps.p
            λ = self.security_param
            t = self.t
            v = max(ceil(2 * λ * log(2,3)), ceil(5 * log(p, 3) / (2*t)))
            h_list, h_len = self.GenHashFamily()
            print(f'h_len : {h_len}')
            # Choose random small ideal
            p = self.precomps.p
            O0 = self.precomps.O0

            q1, q2 = random_prime(floor(p**(1/8))), random_prime(p)
            alpha = FullrepresentInteger(q1 * q2, p)
            I = O0 * alpha + O0 * q1
            assert(I.norm() == q1)

            # generate equivalent ideal paths
            ideal_paths = []
            while len(ideal_paths) != h_len:
                J = self.KLPT_threshold(I, v * t)
                if J : ideal_paths.append(J)

            # long ideal to isogeny paths
            isog_paths = []
            for L in ideal_paths:
                J, _ = make_cyclic(L)
                isog_path = self.LongIdealToIsogeny(J, v)
                isog_paths.append(isog_path)

            if backup_file:
                json_data = {}
                json_data['h_list'] = h_list
                json_data['isog_paths'] = [[[isog_frag.to_list() for isog_frag in isog] for isog in isog_path] for isog_path in isog_paths]
                with open(backup_file, 'w') as f:
                    f.write(json.dumps(json_data))

        pk = isog_paths[0][-1][-1].codomain().curve()
        sk = []
        for party_idx in range(1, self.n + 1):
            partial_sk = []
            for i in range(h_len):
                h = h_list[i]
                partial_sk.append(isog_paths[i][h[party_idx] - 1])
            sk.append(partial_sk)

        return pk, sk, h_list

    def pushforward_sig(self, partial_sig, partial_isog, q):
        a = self.precomps.a

        (P1, Q1), (P2, Q2) = partial_sig
        E_prev = None
        for isog_fragment in partial_isog:
            if E_prev:
                assert E_prev == isog_fragment.domain().j_invariant()
            assert P1.order() == P2.order() == Q1.order() == Q2.order() == 2**a, f"{P1.order().factor()}\n{Q1.order().factor()}\n{P2.order().factor()}\n{Q2.order().factor()}\n"
            assert (4*P1).weil_pairing(4*Q1, 2**(a-2)) * (4*P2).weil_pairing(4*Q2, 2**(a-2)) == 1
            # Compute Pushforward of isog_fragment
            Phi = Dim2Isogeny(((P1, P2), (Q1, Q2)), a - 2, extra = 2, precomps = self.precomps)
            K = isog_fragment._kernel
            deg = isog_fragment._degree
            K = K.curve_point()
            iso = K.curve().isomorphism_to(P1.curve())
            K = iso(K)
            assert K.curve() == P1.curve() == Q1.curve(), f"{P1.curve().j_invariant()}\n{K.curve().j_invariant()}"
            assert K.order() == deg
            _E1 = KummerLine(P1.curve())
            _K = _E1(K[0])
            new_isog_frag = KummerLineIsogeny(_E1, _K, deg)

            E_prev = new_isog_frag.codomain().j_invariant()

            imK = Phi.pushforward_3b(K)#2**(a-2)-q)
            assert imK.curve() == P2.curve() == P2.curve()
            assert imK.order() == deg
            _E2 = KummerLine(P2.curve())
            _imK = _E2(imK[0])
            pushed_isog = KummerLineIsogeny(_E2, _imK, deg)

            # Evaluate P1, P2, Q1, Q2 by isog_fragment and pushed_isog
            _P1, _Q1, _PmQ1 = _E1(P1[0]), _E1(Q1[0]), _E1((P1 - Q1)[0])
            imP1, imQ1, imPmQ1 = new_isog_frag(_P1), new_isog_frag(_Q1), new_isog_frag(_PmQ1)
            imP1, imQ1 = imP1.curve_point(), imQ1.curve_point()
            if (imP1 - imQ1)[0] != imPmQ1.x():
                imQ1 = -imQ1
            assert (imP1 - imQ1)[0] == imPmQ1.x()
            assert new_isog_frag.codomain().curve() == imQ1.curve()

            _P2, _Q2, _PmQ2 = _E2(P2[0]), _E2(Q2[0]), _E2((P2 - Q2)[0])
            imP2, imQ2, imPmQ2 = pushed_isog(_P2), pushed_isog(_Q2), pushed_isog(_PmQ2)
            imP2, imQ2 = imP2.curve_point(), imQ2.curve_point()
            if (imP2 - imQ2)[0] != imPmQ2.x():
                imQ2 = -imQ2
            assert (imP2 - imQ2)[0] == imPmQ2.x()
            assert pushed_isog.codomain().curve() == imQ2.curve()

            P1, Q1, P2, Q2 = imP1, imQ1, imP2, imQ2

        # masking evaluated points (TODO)

        return (P1, Q1), (P2, Q2)

    def sign(self, party_idx, msg, h_list, subset, partial_sk, pk, partial_sig = None, prev = None):
        a = self.precomps.a
        b = self.precomps.b
        p = self.precomps.p
        E0 = self.precomps.E0
        X, Y = self.precomps.basis23

        QA_i, QA_j, QA_k = self.precomps.B.gens()
        _E0 = KummerLine(E0)

        index = self.SelectHashFunc(h_list, subset)
        if index == None : return None
        q, _ = HashToPrime(msg, pk, level = self.level)
        h = h_list[index]
        partial_isog = partial_sk[index]
        isog_idx = h[party_idx]
        if isog_idx == 1:
            # Generate and pushforward the ideal of given norm
            Ir_norm = q * (2**(a-2) - q) * 3**b
            assert gcd(q * (2**(a-2) - q), 3) == 1
            a1, a2, a3, a4 = FullrepresentInteger(Ir_norm, p)
            theta = a1 + a2 * QA_i + a3 * QA_j + a4 * QA_k
            assert theta.reduced_norm() == Ir_norm
            m_theta = self.precomps.matrix_theta23(theta)
            imX, imY = self.precomps.evaluate_matrix23(m_theta)
            imR, imS = (2**a) * imX, (2**a) * imY
            R, S = 2**a * X, 2**a * Y
            try:
                wp_ = imR.weil_pairing(S, 3**b)
                wp = imS.weil_pairing(S, 3**b)
                ## If DLOG exists, then imS is guaranteed to be lin. indep with K3
                discrete_log_pari(wp_, wp, 3**b)
                K3_dual = imS
            except TypeError:
                K3_dual = imR # P3 is guaranteed to be lin. indep with K3

            assert K3_dual.order() == 3**b
            K3_dual = _E0(K3_dual[0])
            phi3 = KummerLineIsogeny(_E0, K3_dual, Integer(3**b))

            ximX = _E0(imX[0])
            ximY = _E0(imY[0])
            ximXY = _E0((imX - imY)[0])

            ximX = phi3(ximX)
            ximY = phi3(ximY)
            ximXY = phi3(ximXY)

            imX = ximX.curve_point()
            imY = ximY.curve_point()

            if (imX - imY)[0] != ximXY.x():
                imY = -imY

            imP, imQ = 3**b * imX, 3**b * imY
            inv_3b = inverse_mod(3**b, 2**a)
            imP, imQ = inv_3b * imP, inv_3b * imQ
            P, Q = 3**b * X, 3**b * Y
            sigma0 = (-q * P, -q * Q), (imP, imQ) 

            # Ir_prime = self.precomps.random_ideal_of_given_norm(Ir_norm, prime=False)
            # sigma0 = IdealToIsogenyQlapotis(Ir_prime, a, precomps = self.precomps)
            # E, P, Q = sigma0.images()
            # sigma0 = self.precomps.E0, self.precomps.basis, E, (P, Q)
            sigma1 = self.pushforward_sig(sigma0, partial_isog, q)
            return (sigma1, 1)
        sigma_cur = self.pushforward_sig(partial_sig, partial_isog, q)
        return (sigma_cur, prev + 1)
    
    def verify(self, msg, sig, pk):
        a = self.precomps.a
        q, _ = HashToPrime(msg, pk, level = self.level)
        (P1, Q1), (P2, Q2) = sig
        E1, E2 = P1.curve(), P2.curve()
        if pk.j_invariant() != E1.j_invariant(): return False
        Phi = Dim2Isogeny(((P1, P2), (Q1, Q2)), a - 2, extra = 2, precomps = self.precomps)
        
        # Check degrees using pairings (TODO)
        Id2 = E2(0)
        D = 2**(a-2)
        Ppk, Qpk, W = torsion_basis_with_pairing_2e(E1, a-2)
        P1, _ = Phi((Ppk, Id2))
        Q1, _ = Phi((Qpk, Id2))

        W1 = P1.weil_pairing(Q1, D)
        Wq = W**q
        Wqinv = Wq ** (-1)
        return W1 in [Wq, Wqinv]

    def test_protocol(self):
        print(f"===({self.t}, {self.n})-threshold start===")

        # pk, sk = tPRISM.keygen(backup_file = 'backup_keys.json')
        pk, sk, h_list = self.keygen(precomp_file = 'backup_keys.json')
        print("Keygen done.")

        # Choose random t parties among n parties
        collab = random.sample(list(range(1, self.n + 1)), self.t)
        print(f'Collaborators : {collab}')
        
        # Get the signing order
        index = self.SelectHashFunc(h_list, collab)
        h = h_list[index]
        collab_index = [(party_idx, h[party_idx]) for party_idx in collab]
        signing_order = [x[0] for x in sorted(collab_index, key=lambda x : x[1])]
        print(f'Signing order : {signing_order}')

        # Message
        msg = b"Sample message"

        # Signing
        partial_sig = None
        for prev, party_idx in enumerate(signing_order):
            partial_sig, _ = self.sign(party_idx, msg, h_list, collab, sk[party_idx - 1], pk, partial_sig = partial_sig, prev = prev)
            print(f"#{prev+1} : {party_idx}-th party has signed.")

        sig = partial_sig
        # Verification
        assert self.verify(msg, sig, pk), "The verification failed"
        print("verification succeed")

        return True


if __name__=="__main__":
    tPRISM = threshold_PRISM_sign(2, 3, level = 1)
    tPRISM.test_protocol()
