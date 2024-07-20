from sage.all import *


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

    def _check_bc_div3(self):
        return (self._b % 3 == 0) and (self._c % 3 == 0)

    def hessian(self):
        assert self._check_bc_div3()
        p = self._a
        q = self._b / 3
        r = self._c / 3
        s = self._d
        return BinaryQF([q * q - p * r, p * s - q * r, r * r - q * s])

    def is_projective(self):
        return self.hessian().is_primitive()

    def discriminant(self):
        return self.hessian().discriminant()
        
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

    def __mul__(self, other):
        """Composition of two binary cubic forms."""
        assert self.is_projective()
        assert other.is_projective()
        raise NotImplementedError

    def inverse(self):
        return BinaryCF([self._a, -self._b, self._c, -self._d])
