
import sys
sys.path.insert(0, '..')

from theta_structures.couple_point import CouplePoint
from theta_isogenies.product_isogeny import EllipticProductIsogeny
from theta_isogenies.product_isogeny_sqrt import EllipticProductIsogenySqrt
from ideal_to_isogeny.endomorphisms import evaluate_endomorphism_type
from applications.PRISM.others.utilities.discrete_log import BiDLP
from applications.PRISM.utilities.supersingular import torsion_basis_with_pairing_3f

class Dim2Isogeny:
    def __init__(self, kernel, n, endomorphisms=[], diagonal_isogenies=[], extra=0, precomps=None, curves=None, **kwds):
        (P1, P2), (Q1, Q2) = kernel
        P=CouplePoint(P1, P2)
        Q=CouplePoint(Q1, Q2)
        if curves:
            self.E1, self.E2 = curves
        else:
            self.E1, self.E2 = P.curves()
        self.precomps=precomps
        kernel=(P, Q)

        self.endomorphisms = endomorphisms
        self.diagonal_isogenies = diagonal_isogenies

        if extra == 0:
            strategy = None
            if not precomps is None:
                strategy = self.precomps.strategy_dim2(n-2)
            self.isogeny = EllipticProductIsogenySqrt(kernel, n, strategy=strategy, **kwds)
        else:
            assert extra == 2 # case extra = 1 not implemented yet
            strategy = None
            if not precomps is None:
                strategy = self.precomps.strategy_dim2(n)
            self.isogeny = EllipticProductIsogeny(kernel, n, strategy=strategy, **kwds)

    def __call__(self, P, lift=True):
        P1, P2 = P

        for type_end in self.endomorphisms:
            P1, P2 = evaluate_endomorphism_type(type_end, P1, P2)

        for φ1φ2 in self.diagonal_isogenies:
            φ1, φ2 = φ1φ2
            P1, P2 = φ1(P1), φ2(P2)

        P=CouplePoint(P1, P2)
        return self.isogeny(P)

    def codomain(self):
        return self.isogeny.codomain()
    
    # input : 3^b-torsion point P in E1[3^b]
    def pushforward_3b(self, P):
        b = self.precomps.b
        p = self.precomps.p

        order = P.order()
        E1 = P.curve()
        len3 = order.valuation(3)
        assert len3 <= b
        
        assert self.E1 == E1, f"E: {E1}\nE1 : {self.E1}\nE2 : {self.E2}"
        E3 = self.E2

        imP, _ = self(CouplePoint(P, E3(0)))

        X3, Y3, _ = torsion_basis_with_pairing_3f(E3, len3)
    
        imX3, _ = self(CouplePoint(E1(0), X3))
        imY3, _ = self(CouplePoint(E1(0), Y3))
        imXmY3, _ = self(CouplePoint(E1(0), X3 - Y3))

        if (imX3 - imY3)[0] != imXmY3[0]:
            imY3 = -imY3

        x, y = BiDLP(imP, imX3, imY3, order)
        assert imP == x * imX3 + y * imY3

        imimP = x * X3 + y * Y3
        assert imimP.curve() == self.E2
        
        return imimP

    def embedded_isogeny(self, degree, basis=None, e=None, ePQ=None):
        """
        Given an isogeny phi embeded via Kani's construction of degree 'degree'.
        And a basis of 2^e-torsion.
        Recover the correct curve in the codomain product, and the correct image of this basis.
        """
        precomps=self.precomps
        if e is None:
            e=precomps.e
        if basis is None:
            basis=precomps.basis
            if ePQ is None:
                ePQ=precomps.eP0Q0(e)
        if ePQ is None:
            ePQ = precomps.pairing(P, Q, e)

        P, Q = basis
        E2 = self.E2
        T1, T2 = P, E2(0)
        S1, S2 = Q, E2(0)
        T = CouplePoint(T1, T2)
        S = CouplePoint(S1, S2)
        TmS = T-S

        # let's evaluate the two-dimensional isogeny on our points
        Phi_P = self(T)
        Phi_Q = self(S)
        Phi_PQ = self(TmS)

        F1, F2 = self.codomain()

        # projection on F1
        Phi_P1 = Phi_P[0]
        Phi_Q1 = Phi_Q[0]
        Phi_PQ1 = Phi_PQ[0]

        # ToOptimize: since we push three points, we only need to lift the first one, the x coordinates of the other two should be enough to recover y(Phi_Q1)
        # fixing the sign knowing the difference between two points
        Phi_P1, Phi_Q1 = fix_minus_sign(Phi_P1, Phi_Q1, Phi_PQ1)

        # projection on F2
        Phi_P2 = Phi_P[1]
        Phi_Q2 = Phi_Q[1]
        Phi_PQ2 = Phi_PQ[1]

        # fixing the sign knowing the difference between two points
        Phi_P2, Phi_Q2 = fix_minus_sign(Phi_P2, Phi_Q2, Phi_PQ2)

        ePQ_deg = ePQ**degree
        # ePQ_inv_deg = ePQ_deg**(-1)

        ePQ_F1 = precomps.pairing(Phi_P1, Phi_Q1, e)
        if ePQ_deg == ePQ_F1:
            return F1, Phi_P1, Phi_Q1
        #elif ePQ_inv_deg == ePQ_F1:
        #    return F1, Phi_P1, -Phi_Q1

        ePQ_F2 = precomps.pairing(Phi_P2, Phi_Q2, e)
        if ePQ_deg == ePQ_F2:
            return F2, Phi_P2, Phi_Q2
        #elif ePQ_inv_deg == ePQ_F2:
        #    return F2, Phi_P2, -Phi_Q2

        raise ValueError("Could not identify correct codomain in embed_isogeny")

# ToOptimize: since we are pushing through φ(PQ), we could gain one sqrt
# when reconstructing Q from x(Q).
# Alternatively since we are using pairings to check the correct codomain,
# we could just not push through φ(PQ)
# Longer term it might make sense to systematically work with a basis P, Q,
# P+Q; this is enough for the arithmetic on a Kummer surface, and would
# gain some sqrt; but some of our arithmetic would be more complicated so
# not sure it is worth it.
def fix_minus_sign(P, Q, PQ):
    """
    TODO: this is redundant, we have similar code in isogenies x only
    clean this up

    We have ±P, ±Q, ±(P - Q).
    This functions outputs either (-P, -Q)
    or (P, Q)
    """
    A = P.curve().a_invariants()[1]

    xP, xQ, xPQ = P[0], Q[0], PQ[0]
    yP, yQ = P[1], Q[1]

    lhs = A + xP + xQ + xPQ
    rhs = ((yQ - yP) / (xQ - xP)) ** 2

    if lhs == rhs:
        Q = -Q

    # Make sure everything now works
    assert A + P[0] + Q[0] + PQ[0] != ((Q[1] - P[1]) / (Q[0] - P[0])) ** 2

    return P, Q

