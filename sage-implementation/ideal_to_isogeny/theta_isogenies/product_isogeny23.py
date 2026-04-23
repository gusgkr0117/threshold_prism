from theta_structures.split_structure import SplitThetaStructure
from theta_structures.couple_point import CouplePoint
from theta_isogenies.morphism import Morphism
from theta_isogenies.gluing_isogeny import GluingThetaIsogeny
from theta_isogenies.isomorphism import SplittingIsomorphism
from theta_isogenies.isogeny import ThetaIsogeny
from theta_isogenies.isogeny33 import ThetaIsogeny33
from utilities.strategy import optimised_strategy

import code

class EllipticProductIsogeny23(Morphism):
    r"""
    Given (P1, P2), (Q1, Q2) in (E1 x E2)[2^(a+2) * 3^b] as the generators of a kernel
    of a (2^a * 3^b, 2^a * 3^b)-isogeny between elliptic products, computes this isogeny

    ker(Phi) = <(P1, P2), (Q1, Q2)> : E1 x E2 -> E3 x E4

    Input:

    - kernel = CouplePoint(P1, P2), CouplePoint(Q1, Q2):
      where points are on the elliptic curves E1, E2 of order 2^(a+2) * 3^b
    - n: the length of the chain
    - strategy: the optimises strategy to compute a walk through the graph of
      images and doublings with a quasli-linear number of steps
    - zeta (optional): a second root of unity

    NOTE: if only the 2^a * 3^b torsion is known, the isogeny should be computed with
    `EllipticProductIsogenySqrt()` which computes the last two steps without the
    torsion above the kernel, but instead with square-root computations (which
    is slower)
    """

    def __init__(self, kernel, a, b, strategy=None, zeta=None):
        self.a = a
        self.b = b
        self.E1, self.E2 = kernel[0].curves()
        self._zeta = zeta
        
        assert kernel[1].curves() == (self.E1, self.E2)

        self._domain = (self.E1, self.E2)

        # if strategy is None:
        #     strategy = self.get_strategy()
        self.strategy22 = self.get_strategy22()
        self.strategy33 = self.get_strategy33()

        self._phis = self.isogeny_chain(kernel)
        T_last = self._phis[-1].codomain()
        self._splitting = SplitThetaStructure(T_last)

        self._codomain = self._splitting.curves()

    def get_strategy22(self):
        return optimised_strategy(self.a)

    def get_strategy33(self):
        return optimised_strategy(self.b, is33 = True)

    def isogeny_chain(self, kernel):
        """
        Compute the codomain of the isogeny chain and store intermediate
        isogenies for evaluation
        """
        # Extract the CouplePoints from the Kernel
        Tp1, Tp2 = kernel
        assert isinstance(Tp1, CouplePoint) and isinstance(Tp2, CouplePoint)

        # Store chain of (2,2)-isogenies
        isogeny_chain = []

        # 1. gluing by (2,2)-isogeny
        # 1-1. computing (2,2)-torsion kernel point
        Tp1, Tp2 = Tp1.triple_iter(self.b), Tp2.triple_iter(self.b) 
        assert Tp1.double_iter(self.a+2)[0].is_zero() and Tp2.double_iter(self.a+2)[1].is_zero()
        # assert not (S.double_iter(2)[0].is_zero() or S.double_iter(2)[1].is_zero())
        # assert R.double_iter(3)[0].is_zero() and R.double_iter(3)[1].is_zero()
        # assert S.double_iter(3)[0].is_zero() and S.double_iter(3)[1].is_zero()
        # phi = GluingThetaIsogeny(R, S)
        # Th = phi.codomain()
        # isogeny_chain.append(phi)
        # TTp1, TTp2 = phi(Tp1), phi(Tp2)

        # ### TEST Triple method of ThetaPoint ###
        # temp1 = TTp1.double_iter(self.a + 1).triple_iter(self.b)
        # temp2 = TTp2.double_iter(self.a + 1).triple_iter(self.b)
        # assert temp1.is_zero() and temp2.is_zero(), "temp1, temp2 : {0}, {1}".format(temp1, temp2)

        # 3. computing (2^a,2^a)-isogeny chain
        strat_idx = 0
        level = [0]
        ker = (Tp1, Tp2)
        kernel_elements = [ker]

        for k in range(self.a):
            prev = sum(level)
            ker = kernel_elements[-1]

            while prev != (self.a - 1 - k):
                level.append(self.strategy22[strat_idx])

                # Perform the Doublings
                Tp1 = ker[0].double_iter(self.strategy22[strat_idx])
                Tp2 = ker[1].double_iter(self.strategy22[strat_idx])

                ker = (Tp1, Tp2)

                # Update kernel elements and bookkeeping variables
                kernel_elements.append(ker)
                prev += self.strategy22[strat_idx]
                strat_idx += 1
            
            # Compute the codomain from the 3-torsion
            Tp1, Tp2 = ker
            if k == 0:
                phi = GluingThetaIsogeny(Tp1, Tp2)
            # elif k == self.a - 2:
            #     phi = ThetaIsogeny(Th, Tp1, Tp2, hadamard=(False, False))
            # elif k == self.a - 1:
            #     phi = ThetaIsogeny(Th, Tp1, Tp2, hadamard=(True, False))
            else:
                try:
                    phi = ThetaIsogeny(Th, Tp1, Tp2)
                except Exception as e:
                    print(e)
                    print(f'k : {k}')
                    raise Exception("error! ThetaIsogeny")

            # Update the chain of isogenies
            Th = phi.codomain()
            isogeny_chain.append(phi)

            # Remove elements from list
            kernel_elements.pop()
            level.pop()

            # Push through points for the next step
            kernel_elements = [(phi(T1), phi(T2)) for T1, T2 in kernel_elements]
            


        assert len(kernel_elements) == 0

        TTp1, TTp2 = kernel
        for f in isogeny_chain:
            # if isinstance(f, GluingThetaIsogeny):
            #     print(f'TTp1 : {TTp1}\nTTp2 : {TTp2}')
            TTp1, TTp2 = f(TTp1), f(TTp2)
            assert not ( TTp1.is_zero() or TTp2.is_zero() ), f"TTp1 : {TTp1}\nTTp2 : {TTp2}"
        tmp1 = TTp1.triple_iter(self.b).double_iter(2)
        tmp2 = TTp2.triple_iter(self.b).double_iter(2)
        assert tmp1.is_zero() and tmp2.is_zero(), f"\ntmp1 : {tmp1}\ntmp2 : {tmp2}"

        # 2. computing (3^b,3^b)-isogeny chain
        Tp1, Tp2 = TTp1.double_iter(2), TTp2.double_iter(2)
        strat_idx = 0
        level = [0]
        ker = (Tp1, Tp2)
        kernel_elements = [ker]

        for k in range(self.b):
            prev = sum(level)
            ker = kernel_elements[-1]

            while prev != (self.b - 1 - k):
                level.append(self.strategy33[strat_idx])

                # Perform the Triplings
                Tp1 = ker[0].triple_iter(self.strategy33[strat_idx])
                Tp2 = ker[1].triple_iter(self.strategy33[strat_idx])

                ker = (Tp1, Tp2)

                # Update kernel elements and bookkeeping variables
                kernel_elements.append(ker)
                prev += self.strategy33[strat_idx]
                strat_idx += 1
            
            # Compute the codomain from the 3-torsion
            Tp1, Tp2 = ker
            phi = ThetaIsogeny33(Th, Tp1, Tp2)

            # Update the chain of isogenies
            Th = phi.codomain()
            isogeny_chain.append(phi)

            # Remove elements from list
            kernel_elements.pop()
            level.pop()

            # Push through points for the next step
            kernel_elements = [(phi(T1), phi(T2)) for T1, T2 in kernel_elements]
        assert len(kernel_elements) == 0
        
        # 4. splitting by (2,2)-isogeny
        splitting_iso = SplittingIsomorphism(Th, zeta=self._zeta)
        isogeny_chain.append(splitting_iso)

        return isogeny_chain

    def evaluate_isogeny(self, P):
        """
        Given a point P, of type CouplePoint on the domain E1 x E2, computes the
        CouplePoint on the codomain ThetaStructure isomorphic to E3 x E4
        """
        if not isinstance(P, CouplePoint):
            raise TypeError(
                "EllipticProductIsogeny isogeny expects as input a CouplePoint on the domain product E1 x E2"
            )
        for f in self._phis:
            P = f(P)
        return P

    def __call__(self, P, lift=True):
        """
        Evaluate a CouplePoint under the action of this isogeny. If lift=True,
        then the affine coordinates of the points are returned, otherwise points
        on the Kummer line are returned.
        """
        image_P = self.evaluate_isogeny(P)
        return self._splitting(image_P, lift=lift)
