from sage.all import *
from sage.algebras.quatalg.quaternion_algebra import *
import random
from itertools import combinations

import sys
sys.path.insert(0, '../..')
sys.path.insert(0, '../../ideal_to_isogeny')

import params
from ideal_to_isogeny.endomorphisms import FullrepresentInteger, iota, pi
from quaternions.ideals import is_cyclic, random_equivalent_ideal, make_cyclic, chi, ideal_generator, small_equivalent_ideal, pullback_ideal
from PRISM.quaternions.klpt import IdealModConstraint, StrongApproximationHeuristic
from ideal_to_isogeny.ideal_to_isogeny_qlapoti23 import IdealToIsogenyQlapotis23
from ideal_to_isogeny.quaternion_helpers.helpers import reduced_ideal
from precomputations_PRSIM import Precomputations_PRISM
from others.utilities.discrete_log import BiDLP
from others.montgomery_isogenies.kummer_isogeny import KummerLineIsogeny
from montgomery_isogenies.kummer_line import KummerLine

def random_function(n, t):
    x = [-1]
    for _ in range(n):
        x.append(random.randint(1, t))
    return x

class threshold_PRISM_sign:
    def __init__(self, precomps = None, level = 1):
        prime = params.levels_threshold[level]['p']
        a = params.levels_threshold[level]['a']
        b = params.levels_threshold[level]['b']
        self.t = params.levels_threshold[level]['t']
        self.n = params.levels_threshold[level]['n']
        self.level = level
        if not precomps:
            precomps = Precomputations_PRISM(prime, 122, a = a, b = b, role='threshold')
        self.precomps = precomps

    def GenHashFamily(self):
        n, t = self.n, self.t
        n_list = list(range(1, n+1))
        t_set = set(range(1, t+1))
        h_list = []
        while True:
            h = random_function(n, t)
            h_list.append(h)
            check = True
            for subset in combinations(n_list, t):
                exist = False
                for h in h_list:
                    im_subset = [h[x] for x in subset]
                    if set(im_subset).issuperset(set(t_set)):
                        exist = True
                        break
                if not exist:
                    check = False
                    break
            if check: break

        return h_list, len(h_list)

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
    def KLPT_threshold(self, I):
        max_attemps = 10
        prime = self.precomps.p
        t = self.t
        b = self.precomps.b
        q1 = Integer(I.norm())
        QA_i, QA_j, QA_k = self.precomps.B.gens()
        for _ in range(max_attemps):
            γ = FullrepresentInteger(q1 * 3**(2*b), prime, primitive=True)
            γ = γ[0] + γ[1] * QA_i + γ[2] * QA_j + γ[3] * QA_k
            C0, D0 = IdealModConstraint(I, γ)
            v = StrongApproximationHeuristic(prime, q1, C0, D0, factor(3**(b*t - 2*b)))
            if v:
                beta = γ * v
                J = chi(beta, I)
                if not is_cyclic(J): continue
                assert(I.is_left_equivalent(J))
                return J
        return None

    # J must be a cyclic 3^{bt}-isogeny
    def LongIdealToIsogeny(self, J):
        b = self.precomps.b
        a = self.precomps.a
        O0 = self.precomps.O0
        E0 = self.precomps.E0

        ϕ_list = []
        m = J.norm().valuation(3)
        t = m // b

        # IdealtoIsogeny for ideals of norm 3^b
        J1 = J + O0 * 3**b
        assert is_cyclic(J1), "J1 is not cyclic"
        assert 3**b % J1.norm() == 0, "J1.norm is {0}".format(J1.norm().factor())

        J1ker = self.IdealToIsogeny3b(J1)
        _E0 = KummerLine(E0)
        _J1ker = _E0(J1ker[0])
        ϕ1 = KummerLineIsogeny(_E0, _J1ker, J1.norm())
        ϕ_list.append(ϕ1)

        J_prev = J1
        prev_steps = J1.norm().valuation(3)
        print(f"total length : {m}")
        while prev_steps < m:
            assert is_cyclic(J_prev)
            J_prev_red = reduced_ideal(J_prev.conjugate()).conjugate()
            # print("J_prev_red norm", J_prev_red.norm())
            while True:
                K, _, _ = random_equivalent_ideal(J_prev_red, adjust_right_order=True)
                if K.norm() % 3 != 0: break
            assert K.is_right_equivalent(J_prev)
            # print(f'K norm : {K.norm()}')
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
            nJi = Ji.norm()
            assert is_cyclic(Ji), "Ji is not cyclic"
            assert 3**b % nJi == 0, "Ji.norm is {0}".format(nJi)
            prev_steps += nJi.valuation(3)

            Jiker = self.IdealToIsogeny3b(Ji)

            phi_aux = IdealToIsogenyQlapotis23(K, a, b, self.precomps, allow_diags=False)
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
            ϕ_list.append(ϕi)
            J_prev = J_prev * (Jilong + Jilong.left_order() * 3**b)
            print('prev_steps:', prev_steps)

        return ϕ_list
    
    def gen_graph_structure(self):
        # Choose random small ideal
        p = self.precomps.p
        O0 = self.precomps.O0

        q1, q2 = random_prime(ceil(p**(1/8))), random_prime(p)
        alpha = FullrepresentInteger(q1 * q2, p)
        I = O0 * alpha + O0 * q1
        assert(I.norm() == q1)

        # generate equivalent ideal paths
        ideal_paths = []
        for _ in range(2):
            ideal_paths.append(self.KLPT_threshold(I))
        assert len(ideal_paths) != 0

        # long ideal to isogeny paths
        isog_paths = []
        for L in ideal_paths:
            J, _ = make_cyclic(L)
            isog_path = self.LongIdealToIsogeny(J)
            isog_paths.append(isog_path)

        return isog_paths
    
    def keygen(self):
        h_list, h_len = self.GenHashFamily()
        print(f'h_len : {h_len}')
        # Choose random small ideal
        p = self.precomps.p
        O0 = self.precomps.O0

        q1, q2 = random_prime(ceil(p**(1/8))), random_prime(p)
        alpha = FullrepresentInteger(q1 * q2, p)
        I = O0 * alpha + O0 * q1
        assert(I.norm() == q1)

        # generate equivalent ideal paths
        ideal_paths = []
        for _ in range(h_len):
            ideal_paths.append(self.KLPT_threshold(I))
        assert len(ideal_paths) != 0

        # long ideal to isogeny paths
        isog_paths = []
        for L in ideal_paths:
            J, _ = make_cyclic(L)
            isog_path = self.LongIdealToIsogeny(J)
            isog_paths.append(isog_path)

        pk = isog_paths[0][self.t - 1].codomain()

        return pk, isog_paths

tPRISM = threshold_PRISM_sign()
pk, sk = tPRISM.keygen()