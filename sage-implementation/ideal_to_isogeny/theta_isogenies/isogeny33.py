from sage.all import ZZ

from theta_structures.dimension_two import ThetaStructure, ThetaPoint
from theta_isogenies.morphism import Morphism
from utilities.batched_inversion import batched_inversion


class ThetaIsogeny33(Morphism):
    def __init__(self, domain, T1_8, T2_8, hadamard=(False, True)):
        """
        Compute a (3,3)-isogeny in the theta model. Expects as input:

        - domain: the ThetaStructure from which we compute the isogeny
        - (T1_8, T2_8): points of 8-torsion above the kernel generating the isogeny

        When the 8-torsion is not available (for example at the end of a long
        (3,3)-isogeny chain), the the helper functions in isogeny_sqrt.py
        must be used.

        NOTE: on the hadamard bools:

        The optional parameter 'hadamard' controls if we are in standard or dual
        coordinates, and if the codomain is in standard or dual coordinates. By
        default this is (False, True), meaning we use standard coordinates on
        the domain A and the codomain B.

        The kernel is then the kernel K_2 where the action is by sign. Other
        possibilities: - (False, False): standard coordinates on A, dual
        coordinates on B - (True, True): start in dual coordinates on A
        (alternatively: standard coordinates on A but quotient by K_1 whose
        action is by permutation), and standard coordinates on B. - (True,
        False): dual coordinates on A and B

        These can be composed as follows for A -> B -> C:

        - (False, True) -> (False, True) (False, False) -> (True, True):
          - standard coordinates on A and C,
          - standard/resp dual coordinates on B
        - (False, True) -> (False, False) (False, False) -> (True, False):
          - standard coordinates on A,
          - dual coordinates on C,
          - standard/resp dual coordinates on B
        - (True, True) -> (False, True) (True, False) -> (True, True):
          - dual coordinates on A,
          - standard coordinates on C,
          - standard/resp dual coordiantes on B
        - (True, True) -> (False, False) (True, False) -> (True, False):
          - dual coordinates on A and C
          - standard/resp dual coordinates on B

        On the other hand, these gives the multiplication by [2] on A:

        - (False, False) -> (False, True) (False, True) -> (True, True):
          - doubling in standard coordinates on A
          - going through dual/standard coordinates on B=A/K_2
        - (True, False) -> (False, False) (True, True) -> (True, False):
          - doubling in dual coordinates on A
          - going through dual/standard coordinates on B=A/K_2
            (alternatively: doubling in standard coordinates on A going
            through B'=A/K_1)
        - (False, False) -> (False, False) (False, True) -> (True, False):
          - doubling from standard to dual coordinates on A
        - (True, False) -> (False, True) (True, True) -> (True, True):
          - doubling from dual to standard coordinates on A
        """
        if not isinstance(domain, ThetaStructure):
            raise ValueError
        self._domain = domain
        self._coeffs = None
        self._hadamard = hadamard
        self._precomputation = None
        self._codomain = self._compute_codomain(T1_8, T2_8)
    
    def _fourwaymult(v, w):
        return [v[0] * w[0], v[1] * w[1], v[2] * w[2], v[3] * w[3]]

    def _compute_codomain(self, R : ThetaPoint, S : ThetaPoint):
        """
        Given two isotropic points of 3-torsion R and S, compatible with
        the theta null point, compute the level two theta null point A/K_2
        """
        TC = self._domain.triple_constants()
        a = TC[0][0]
        b = TC[0][1]
        c = TC[0][2]
        d = TC[0][3]

        XR, ZR, YR, TR = R.coords()

        XS, ZS, YS, TS = S.coords()
        
        sO = TC[1]
        hO_inv = TC[4]

        # Constructing the isogeny coefficients 
        # print(f"Constructing the isogeny coefficients ...\n")
        
        ab = a * b
        ac = a * c
        ad = a * d
        bc = b * c
        bd = b * d
        cd = c * d
        d1p = ab + cd 
        d1m = ab - cd
        d2p = ac + bd 
        d2m = ac - bd
        d3p = ad + bc
        d3m = ad - bc
        
        D1 = d1p * d1m
        D2 = d2p * d2m
        D3 = d3p * d3m

        D12 = D1 * D2
        D13 = D1 * D3
        D23 = D2 * D3

        hR = ThetaPoint.to_squared_theta_fast_kummer(XR, YR, ZR, TR)
        hS = ThetaPoint.to_squared_theta_fast_kummer(XS, YS, ZS, TS)
        hRO = ThetaPoint.to_fourwaymult(hR, hO_inv)
        hSO = ThetaPoint.to_fourwaymult(hS, hO_inv)

        HR = ThetaPoint.to_hadamard_fast_kummer(*hRO)
        HS = ThetaPoint.to_hadamard_fast_kummer(*hSO)

        RXX = HR[0]
        RYY = HR[1]
        RZZ = HR[2]
        RTT = HR[3]
        SXX = HS[0]
        SYY = HS[1]
        SZZ = HS[2]
        STT = HS[3]

        XYR = XR * YR
        XZR = XR * ZR
        XTR = XR * TR
        YZR = YR * ZR
        YTR = YR * TR
        ZTR = ZR * TR
        XYS = XS * YS
        XZS = XS * ZS
        XTS = XS * TS
        YZS = YS * ZS
        YTS = YS * TS
        ZTS = ZS * TS

        Rsig = d1m * (XYR + ZTR)
        Rdel = d1p * (XYR - ZTR)
        Ssig = d1m * (XYS + ZTS)
        Sdel = d1p * (XYS - ZTS)
        RXY = Rsig + Rdel
        RZT = Rsig - Rdel
        SXY = Ssig + Sdel
        SZT = Ssig - Sdel

        Rsig = d2m * (XZR + YTR)
        Rdel = d2p * (XZR - YTR)
        Ssig = d2m * (XZS + YTS)
        Sdel = d2p * (XZS - YTS)
        RXZ = Rsig + Rdel
        RYT = Rsig - Rdel
        SXZ = Ssig + Sdel
        SYT = Ssig - Sdel

        Rsig = d3m * (XTR + YZR)
        Rdel = d3p * (XTR - YZR)
        Ssig = d3m * (XTS + YZS)
        Sdel = d3p * (XTS - YZS)
        RXT = Rsig + Rdel
        RYZ = Rsig - Rdel
        SXT = Ssig + Sdel
        SYZ = Ssig - Sdel

        c2 = D23 * SXY
        c2 = c2 + (D13 * SXZ)
        c2 = c2 + (D12 * SXT)

        d2 = D23 * RXY
        d2 = d2 + (D13 * RXZ)
        d2 = d2 + (D12 * RXT)

        E1 = (d2 * SZT) - (c2 * RZT)
        E1 = E1 * D23

        E2 = (SXX * RYY) - (RXX * SYY)

        E1R = E1 * RXX
        E1S = E1 * SXX
        E2c = E2 * c2
        E2d = E2 * d2

        u1 = E1R * SXX
        u1 = u1 + u1

        u2 = (E1S * RYY) + (E1R * SYY)
        tmp = (E2d * SZT) + (E2c * RZT)
        tmp = tmp * D23
        u2 = u2 + tmp

        u3 = E1S * RZZ
        u3 = u3 + (E1R * SZZ)
        tmp = (E2d * SYT) + (E2c * RYT)
        tmp = tmp * D13
        u3 = u3 + tmp

        u4 = E1S * RTT
        u4 = u4 + (E1R * STT)
        tmp = (E2d * SYZ) + (E2c * RYZ)
        tmp = tmp * D12
        u4 = u4 + tmp

        u5 = E2c * d2
        u5 = u5 + u5

        self._coeffs = [u1,u2,u3,u4,u5]

        u5ab = u5 * ab
        u5cd = u5 * cd

        a2 = sO[0]
        b2 = sO[1]
        c2 = sO[2]
        d2 = sO[3]
        
        aa = u1 * a2
        aa = aa + (u2 * b2)
        aa = aa + (u3 * c2)
        aa = aa + (u4 * d2)
        aa = aa * a
        aa = aa + (u5cd * b)
        
        bb = u1 * b2
        bb = bb + (u2 * a2)
        bb = bb + (u3 * d2)
        bb = bb + (u4 * c2)
        bb = bb * b
        bb = bb + (u5cd * a)

        cc = u1 * c2
        cc = cc + (u2 * d2)
        cc = cc + (u3 * a2)
        cc = cc + (u4 * b2)
        cc = cc * c
        cc = cc + (u5ab * d)

        dd = u1 * d2
        dd = dd + (u2 * c2)
        dd = dd + (u3 * b2)
        dd = dd + (u4 * a2)
        dd = dd * d
        dd = dd + (u5ab * c)
        
        image_thetas = (aa,cc,bb,dd)
        return ThetaStructure(image_thetas)

    def __call__(self, P):
        """
        Take into input the theta null point of A/K_2, and return the image
        of the point by the isogeny
        """
        if not isinstance(P, ThetaPoint):
            raise TypeError("Isogeny evaluation expects a CouplePoint as input")
        a, b, c, d = P.coords()
        P = (a, c, b, d)
        P2 = ThetaPoint.to_squared(*P)

        u4xy = self._coeffs[4] * (P[0] * P[1])
        u4zt = self._coeffs[4] * (P[2] * P[3])

        p1 = self._coeffs[0] * P2[0]
        p1 = p1 + (self._coeffs[1] * P2[1])
        p1 = p1 + (self._coeffs[2] * P2[2])
        p1 = p1 + (self._coeffs[3] * P2[3])
        p1 = P[0] * p1
        p1 = p1 + (u4zt * P[1])

        p2 = self._coeffs[0] * P2[1]
        p2 = p2 + (self._coeffs[1] * P2[0])
        p2 = p2 + (self._coeffs[2] * P2[3])
        p2 = p2 + (self._coeffs[3] * P2[2])
        p2 = P[1] * p2
        p2 = p2 + (u4zt * P[0])

        p3 = self._coeffs[0] * P2[2]
        p3 = p3 + (self._coeffs[1] * P2[3])
        p3 = p3 + (self._coeffs[2] * P2[0])
        p3 = p3 + (self._coeffs[3] * P2[1])
        p3 = P[2] * p3
        p3 = p3 + (u4xy * P[3])

        p4 = self._coeffs[0] * P2[3]
        p4 = p4 + (self._coeffs[1] * P2[2])
        p4 = p4 + (self._coeffs[2] * P2[1])
        p4 = p4 + (self._coeffs[3] * P2[0])
        p4 = P[3] * p4
        p4 = p4 + (u4xy * P[2])
        
        return self._codomain((p1, p3, p2, p4))

        # if self._hadamard[0]:
        #     xx, yy, zz, tt = ThetaPoint.to_squared_theta(
        #         *ThetaPoint.to_hadamard(*P.coords())
        #     )
        # else:
        #     xx, yy, zz, tt = P.squared_theta()

        # Bi, Ci, Di = self._precomputation

        # yy = yy * Bi
        # zz = zz * Ci
        # tt = tt * Di

        # image_coords = (xx, yy, zz, tt)
        # if self._hadamard[1]:
        #     image_coords = ThetaPoint.to_hadamard(*image_coords)
        # return self._codomain(image_coords)
