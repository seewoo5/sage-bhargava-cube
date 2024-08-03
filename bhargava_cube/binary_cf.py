from sage.all import *

from .utils import quad_ring, norm, trace, conj, xgcd_


class BinaryCF(SageObject):
    """Binary cubic form."""
    def __init__(self, abcd):
        if abcd is None:
            abcd = [0, 0, 0, 0]
        if isinstance(abcd, (list, tuple)):
            if len(abcd) != 4:
                raise TypeError("Binary cubic form must be given by a list of three coefficients")
            self._a, self._b, self._c, self._d = [ZZ(x) for x in abcd]
        elif isinstance():
            # Initialize from a cubic homogenous bivariate polynomial
            f = abcd
            from sage.rings.polynomial.multi_polynomial_element import is_MPolynomial
            if f.is_zero():
                self._a, self._b, self._c, self._d = [ZZ(0), ZZ(0), ZZ(0), ZZ(0)]
            elif (is_MPolynomial(f) and f.is_homogeneous() and f.base_ring() == ZZ 
                    and f.degree() == 3 and f.parent().ngens() == 3):
                x, y = f.parent().gens()
                self._a, self._b, self._c, self._d = [f.monomial_coefficient(mon) for mon in [x**3, (x**2)*y, x*(y**2), y**3]]
            else:
                raise TypeError("Binary quadratic form must be given by a cubic homogeneous bivariate integer polynomial")

    def __getitem__(self, n):
        return (self._a, self._b, self._c, self._d)[n]

    def _abcd(self):
        return (self._a, self._b, self._c, self._d)

    def is_bc_div3(self):
        return (self._b % 3 == 0) and (self._c % 3 == 0)

    def hessian(self):
        assert self.is_bc_div3()
        p = self._a
        q = self._b // 3
        r = self._c // 3
        s = self._d
        return BinaryQF([q * q - p * r, p * s - q * r, r * r - q * s])

    def is_projective(self):
        return self.hessian().is_primitive()

    def discriminant(self):
        a, b, c, d = self._abcd()
        b_ = b / 3
        c_ = c / 3
        disc = (a * d) ** 2 - 3 * (b_ * c_) ** 2 - 6 * a * b_ * c_ * d + 4 * (a * c_ ** 3 + b_ ** 3 * d)
        return disc
        
    @staticmethod
    def id(D):
        """Identity element in the class group of binary cubic forms of discriminant D."""
        assert isinstance(D, ZZ)
        if D % 4 == 0:
            return BinaryCF([0, 3, 0, D / 4])
        elif D % 4 == 1:
            return BinaryCF([0, 3, 3, (D + 3) / 4])
        else:
            raise ValueError("D should be 0 or 1 modulo 4")

    def _cs(self):
        assert self.is_bc_div3()
        eps = self.discriminant() % 4
        a0, a1, a2, a3 = self._abcd()
        a1, a2 = a1 // 3, a2 // 3
        c0 = ZZ((2 * a2 ** 3 - 3 * a0 * a1 * a2 + a0 * a0 * a3 - eps * a0) / 2)
        c1 = ZZ((a1 * a1 * a2 - 2 * a0 * a2 * a2 + a0 * a1 * a3 - eps * a1) / 2)
        c2 = ZZ(-(a1 * a2 * a2 - 2 * a1 * a1 * a3 + a0 * a2 * a3 + eps * a2) / 2)
        c3 = ZZ(-(2 * a2 ** 3 - 3 * a1 * a2 * a3 + a0 * a3 * a3 + eps * a3) / 2)
        return (c0, c1, c2, c3)

    def __mul__(self, other):
        """
        Composition of two binary cubic forms.
        Based on the article "Composition and Bhargava's Cubes" by Florian Bouyer.
        """
        assert self.is_projective()
        assert other.is_projective()

        D = ZZ(self.discriminant())
        eps = D % 4
        assert eps in [0, 1]
        
        # Quadratic ring of discriminant D with generator
        R, t = quad_ring(D)
        
        # c_i and c_i'
        _, cs1, cs2, _ = self._cs()
        _, co1, co2, _ = other._cs()
        as1, as2 = self[1] // 3, self[2] // 3
        ao1, ao2 = other[1] // 3, other[2] // 3

        # I = <alpha, beta>, I' = <alpha', beta'>
        alphas = R(cs1 + as1 * t)
        betas = R(cs2 + as2 * t)
        betas_conj = conj(betas, D)
        alphao = R(co1 + ao1 * t)
        betao = R(co2 + ao2 * t)
        betao_conj = conj(betao, D)
        
        # Norms and traces
        NIs = abs(cs1 * as2 - cs2 * as1)
        NIo = abs(co1 * ao2 - co2 * ao1)
        Nas = norm(alphas, D)
        Nao = norm(alphao, D)
        Nbs = norm(betas, D)
        Nbo = norm(betao, D)
        Tr_abs = trace(alphas * betas_conj, D)
        Tr_abo = trace(alphao * betao_conj, D)
        e1 = ZZ(Nas / NIs)
        e2 = ZZ(Nao / NIo)
        e3 = ZZ((NIo * Tr_abs + NIs * Tr_abo) / (2 * NIs * NIo))
        e, n1, n2, n3 = xgcd_([e1, e2, e3])
        m = ZZ(2 * Nas * Nao / (e * e * NIs * NIo))
        B = ZZ(n1 * ((e1 / e) * (Tr_abo / NIo)) + n2 * ((e2 / e) * (Tr_abs / NIs)) + n3 * ((Tr_abs * Tr_abo + NIs * NIo * D) / (2 * e * NIs * NIo)))
        B = B % m
        
        # Coefficients of composition
        z_ = R(-(B + eps) / 2 + t)
        z0 = ((alphas * alphao) ** 2) * conj(betas * betao, D)
        z1 = z0 * z_
        z2 = z1 * z_
        z3 = z2 * z_

        Nb = Nbs * Nbo
        NN = NIs * NIo / Nas / Nao

        a0_ = ZZ(z0[1] / (Nb * (e ** 3)))
        a1_ = ZZ(z1[1] * NN / (Nb * e))
        a2_ = ZZ(z2[1] * (NN ** 2 * e) / Nb)
        a3_ = ZZ(z3[1] * (NN ** 3 * e ** 3) / Nb)
        return BinaryCF([a0_, 3 * a1_, 3 * a2_, a3_])

    def inverse(self):
        return BinaryCF([self._a, -self._b, self._c, -self._d])

    def to_cubic_ring(self):
        """
        Return the associated cubic ring, following Delone-Fadeev and Gan-Gross-Savin.
        It is a ring R = Z<1, \omega, \theta> with relations

        \omega \theta = -ad
        \omega^2 = -ac + b\omega - a\theta
        \theta^2 = -bd + d\omega - c\theta
        """
        a, b, c, d = self._abcd()
        P = ZZ['omega,theta']
        o, t = P.gens()
        I = P.ideal([o * t + a * d, o ** 2 + a * c - b * o + a * t, t ** 2 + b * d - d * o + c * t])
        R = P.quotient_ring(I)
        return R

    def is_reduced(self):
        return self.hessian.is_reduced()

    def reduced_form(self):
        """
        Reduced form of a cubic form under GL(2,ZZ) equivalence.
        Based on the article "Reduction of binary cubic and quartic forms" by J. E. Cremona.

        TODO:
        - Reduced form under the SL(2,ZZ) equivalence
        - Return transformation matrix together
        """
        D = self.discriminant()
        if D == 0:
            raise ValueError("Discriminant has to be nonzero.")

        a_, b_, c_, d_ = self._abcd()
        if D > 0:
            while True:
                k = ZZ(round(-(b_ * c_ - 9 * a_ * d_) / (2 * (b_ * b_ - 3 * a_ * c_))))
                b_, c_, d_ = 3 * a_ * k + b_, 3 * a_ * k ** 2 + 2 * b_ * k + c_, a_ * k ** 3 + b_ * k ** 2 + c_ * k + d_
                if b_ ** 2 - 3 * a_ * c_ > c_ ** 2 - 3 * b_ * d_:
                    a_, b_, c_, d_ = d_, -c_, b_, -a_
                else:
                    break
        else:  # D < 0
            raise NotImplementedError("Not implemented for negative discriminant")
        return BinaryCF([a_, b_, c_, d_])
        

    def __repr__(self):
        return f"BinaryCF(a={self._a},b={self._b},c={self._c},d={self._d})"

    def __str__(self):
        return repr(self)
