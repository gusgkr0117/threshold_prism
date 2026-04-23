import sys
sys.path.insert(0, '..')

import random

from sage.all import (
    ZZ,
    ceil, 
    inverse_mod,
    gcd, 
    randint, 
    cached_method,
    Integers,
    Matrix,
    vector,
    factor
)

import time

from qlapoti23 import qlapoti23
from quaternion_helpers.helpers import *
from quaternion_helpers.short_vec import *
from ideal_to_isogeny.dim23_wrapper import Dim23Isogeny
from endomorphisms import *
from theta_structures.couple_point import CouplePoint
from utilities.pairing import weil_pairing_power_two

class IdealToIsogenyQlapotis23:
    def __init__(self, J, e2_target, e3_target, precomps, allow_diags = True):
        """
        For a given ideal J, compute the isogeny phi_J : E0 -> EJ
        """

        self.precomps = precomps
        self.representation = None
        self.O0 = precomps.O0
        self.e2_target = e2_target
        self.e3_target = e3_target
        self.J = J
        self.nJ = ZZ(J.norm())
        self._count = (None, None)
        self.allow_diags = allow_diags


    def short_equivalent_ideals(self):
        """
        Given an ideal I of norm N, we find two equivalent ideals I1, I2 of
        coprime odd norms d1, d2 such that such that d1 + d2 = 2 ^ f for some
        f>0
        """
        J = self.J

        e2 = self.e2_target - 2
        e3 = self.e3_target

        # Temporary measure
        # TODO : update for non-gluing case in https://eprint.iacr.org/2025/1604
        mu1, mu2, d1, d2, θ, N, I, betaij, e1, e2 = qlapoti23(J, e2, e3, allow_diags = self.allow_diags, odd_norm_output = True)
            

        assert mu1 in self.O0
        assert mu2 in self.O0
        assert θ in self.O0
        # print(mu1 == make_primitive(mu1, self.O0))
        # print(θ == make_primitive(θ, self.O0))
        self.nI = N
        self.I = I

        return mu1, mu2, d1, d2, θ, betaij, e1, e2

    def get_representation(self):
        """
        Given an ideal I of norm N, compute the data needed for the
        isogeny. This function only works on the quaternion side.
        """
        if self.representation is None:
            self.representation = self.short_equivalent_ideals()
        return self.representation

    def _precomp_pairings(self, theta, d1, type_end):
        ew0 = self.precomps.eWP0Q023
        P0, Q0 = self.precomps.basis23
        
        eP2Q2 = ew0**(theta.reduced_norm())
        eP1Q1 = ew0**(d1**2)

        pair_map23 = self.precomps.pair_map23
        if type_end == 1:
            # Need e(P1, Q1)e(P1, Q2)e(P2, Q1)e(P2, Q2)
            x1, x2, x3, x4 = list(theta)
            eP0Q2 = (
                pair_map23['11']**x1 * pair_map23['1i']**x2 *
                pair_map23['1j']**x3 * pair_map23['1k']**x4
            )
            eP2Q0 = (
                pair_map23['11']**x1 * pair_map23['i1']**x2 *
                pair_map23['j1']**x3 * pair_map23['k1']**x4
            )

            eP2Q1 = (eP2Q0 ** d1)
            eP1Q2 = (eP0Q2 ** d1)
            w1 = eP1Q1 * eP2Q1
            w2 = eP2Q2 * eP1Q2
            return w1 * w2, [w1, w2]
        
        elif type_end == 2:
            # Need e(iP1, iQ1)*e(iP1, Q2) * e(P2, iQ1) * e(P2, Q2)
            x1, x2, x3, x4 = list(theta)
            eiP0Q2 = (
                pair_map23['i1']**x1 * pair_map23['ii']**x2 *
                pair_map23['ij']**x3 * pair_map23['ik']**x4
            )
            eP2iQ0 = (
                pair_map23['1i']**x1 * pair_map23['ii']**x2 *
                pair_map23['ji']**x3 * pair_map23['ki']**x4
            )

            eP2iQ1 = (eP2iQ0 ** d1)
            eiP1Q2 = (eiP0Q2 ** d1)
            w1 = eP1Q1 * eP2iQ1
            w2 = eP2Q2 * eiP1Q2
            return w1 * w2, [w1, w2]
        else:
            raise NotImplementedError('aaa')

    def fix_end(self, ker_Phi, e1, e2, d1, theta):
        precomps = self.precomps
        P0, Q0 = precomps.basis23

        (P1, P2), (Q1, Q2) = ker_Phi

        
        # t0 = time.time()

        prods = []
        f1 = e1
        f2 = e2

        theta2 = tuple(i % 2 for i in list(theta))
        kk = {
            (0, 0, 0, 1):1,
            (0, 1, 1, 1):1,
            (1, 0, 1, 1):2,
            (0, 0, 1, 0):2
        }
        type_end = kk[theta2]
        ends = [type_end]

        if type_end == 1:
            thetap = d1 + theta
            
        else: 
            i,_,_ = self.precomps.B.gens()
            thetap = d1*i + theta
            
        num_prods = thetap.reduced_norm().valuation(2) - 2
        num_prods3 = thetap.reduced_norm().valuation(3)
        print(f'num_prods : {num_prods}, num_prods3 : {num_prods3}')
        f1 -= 1
        

        P1, P2 = evaluate_endomorphism_type(type_end, P1, P2)
        Q1, Q2 = evaluate_endomorphism_type(type_end, Q1, Q2)

        # t1 = time.time()
        # print(f'End time: {t1-t0:.3f}s')


        # Compute pairings (forgetting the multiplication by 2^c)
        _, e_prodtype = self._precomp_pairings(theta, d1, type_end)
        # num_prods = f1 - order_pairing(e_numprods) + 1
        
        # Product steps
        prod_type = None
        if num_prods or num_prods3:
            if e_prodtype[0] ** (2**(f1+2) * 3**f2) == e_prodtype[1] ** (2**(f1+2) * 3**f2):
                prod_type = 'Q'
            else:
                prod_type = 'P'

        print(f'prod_type : {prod_type}')
        # t2 = time.time()
        # print(f'Prod detect: {t2-t1:.3f}s')
        # print(f"We have to do {num_prods} product(s)...")

        if prod_type == 'P':
            cof2 = 2**(f1 - num_prods) * 3**(f2 - num_prods3)
            K1 = cof2 * P1
            K2 = cof2 * Q2

        elif prod_type == 'Q':
            cof2 = 2**(f1 - num_prods) * 3**(f2 - num_prods3)
            K1 = cof2 * Q1
            K2 = cof2 * P2

        if num_prods > 0 or num_prods3 > 0:
            K1, K2 = 4 * K1, 4 * K2
            # K1_order, K2_order = K1.order(), K2.order()
            # assert K1_order == K2_order
            # K1, K2 = (K1_order / (2**num_prods)) * K1, (K2_order / (2**num_prods)) * K2
            # assert K1.order() == K2.order() == 2**num_prods, f"K1.order = {K1.order()}, K2.order = {K2.order()}"
            # K1._order = ZZ(2**num_prods)
            # K2._order = ZZ(2**num_prods)
            _phi1 = K1.curve().isogeny(K1)
            _phi2 = K2.curve().isogeny(K2)
            prods.append([_phi1, _phi2])
            P1, Q1 = _phi1(P1), _phi1(Q1)
            P2, Q2 = _phi2(P2), _phi2(Q2)
            f1 -= num_prods
            f2 -= num_prods3

        # t3 = time.time()
        # print(f'Do prod time: {t3 - t2:.3f}s')
        assert P1.order() == P2.order() == 2**(f1 + 2) * 3**f2, f"\nf1={f1}\nP1.order() = {P1.order().factor()}\nP2.order() = {P2.order().factor()}"
        assert Q1.order() == Q2.order() == 2**(f1 + 2) * 3**f2, f"\nf1={f1}\nQ1.order() = {Q1.order().factor()}\nQ2.order() = {Q2.order().factor()}"
        
        ker_Phi = ((P1, P2), (Q1, Q2))

        # Non-product steps
        Phi = Dim23Isogeny(
                ker_Phi,
                f1, f2,
                extra = 2,
                endomorphisms = ends,
                diagonal_isogenies = prods,
                curves = [P0.curve() for _ in range(2)],
                precomps=self.precomps)

        EI, PI, QI = Phi.embedded_isogeny(
                basis=(P0, Q0),
                degree=d1, ePQ=precomps.eWP0Q023)
        # t4 = time.time()
        # print(f'HD time: {t4-t3:.3f}s')
        return EI, PI, QI


    @cached_method
    def images(self):
        """
        Given an ideal I of norm N, this function computes the isogeny
        φI : E0 -> EI.
        Given the 2^e*3^f-torsion canonical basis <R0, S0> we compute φI(R0) and
        φI(S0)
        """

        precomps = self.precomps
        R0, S0 = precomps.basis23
        a = precomps.a
        b = precomps.b

        # let's find two equivalent ideals of short norm d1 and d2
        # such that d1 + d2 = 2^a * 3^b
        mu1, mu2, d1, d2, theta, betaij, e1, e2 = self.get_representation()
        # # let's evaluate theta
        # x1, x2, x3, x4 = theta.coefficient_tuple()
        # c1 = ZZ(2 * x1)
        # c2 = ZZ(2 * x2)
        # c3 = ZZ(2 * x3)
        # c4 = ZZ(2 * x4)
        # P_ = c1 * R0 + c2 * precomps.iota(R0) + c3 * precomps.pi(R0) + c4 * precomps.iota(precomps.pi(R0))
        # Q_ = c1 * S0 + c2 * precomps.iota(S0) + c3 * precomps.pi(S0) + c4 * precomps.iota(precomps.pi(S0))
        # P_ = P_.division_points(2)[0]
        # Q_ = Q_.division_points(2)[0]
        # let's evaluate θ
        theta_m = precomps.matrix_theta23(theta)
        P_, Q_ = self.precomps.evaluate_matrix23(theta_m)

        # Compute the isogeny corresponding to I1 = I*(mu1_bar)/n(I)
        P1 = 2**(a - e1 - 2) * d1 * R0
        P2 = 2**(a - e1 - 2) * P_
        Q1 = 2**(a - e1 - 2) * d1 * S0
        Q2 = 2**(a - e1 - 2) * Q_
        assert (d1 % 3 != 0)
        assert (d2 % 3 != 0)

        ker_Phi = ((P1, P2), (Q1, Q2))
        # assert (P1.order() == 2**(e1 + 2) * 3**e2), "P1.order = {0}".format(P1.order().factor())
        # assert (P2.order() == 2**(e1 + 2) * 3**e2), "P2.order = {0}".format(P2.order().factor())
        # assert (Q1.order() == 2**(e1 + 2) * 3**e2), "Q1.order = {0}".format(Q1.order().factor())
        # assert (Q2.order() == 2**(e1 + 2) * 3**e2), "Q2.order = {0}".format(Q2.order().factor())
        # pair_e = (4*P1).weil_pairing((4*Q1), 2**e1 * 3**e2) * (4*P2).weil_pairing(4*Q2, 2**e1 * 3**e2)
        # assert pair_e == 1, f"pairing : {pair_e}"
        # Cmon sage
        p = Q1.curve().base().characteristic()

        end_to_fix = all(ci in ZZ for ci in list(theta))

        #assert not end_to_fix

        if end_to_fix:
            t0 = time.time()
            print("fix_end!")
            EI, PI, QI = self.fix_end(ker_Phi, e1, e2, d1, theta)
            t1 = time.time()
            # print(f'Hd with stuff: {t1 - t0:.3f}s')

        else:
            t0 = time.time()
            Phi = Dim23Isogeny(
                    ker_Phi,
                    e1, e2,
                    extra = 2,
                    precomps=self.precomps)

            EI, PI, QI = Phi.embedded_isogeny(
                    basis=(R0, S0),
                    degree=d1, ePQ=precomps.eWP0Q023)
            t1 = time.time()
            # print(f'Only hd: {t1 - t0:.3f}s')

        # TODO: remove
        # ePQ0 = precomps.eP0Q0(e)
        # ePQI = precomps.pairing(PI, QI, e)
        # assert ePQ0 ** d1 == ePQI

        # Now compute J
        theta = mu1 * betaij # Generator of J*I1_bar
        theta /= self.nI

        theta_m = precomps.matrix_theta23(theta)
        d1_inv = inverse_mod(d1, 2**a * 3**b)
        theta_m *= d1_inv

        PJ, QJ = self.precomps.evaluate_matrix23(theta_m, (PI, QI))
        # TODO: remove
        # O0 = theta.parent().maximal_order()
        # print(f'{theta in O0 = }')
        # ePQ0 = precomps.eP0Q0(e)
        # ePQJ = precomps.pairing(PJ, QJ, e)
        # assert ePQ0 ** self.nJ == ePQJ

        return EI, PJ, QJ