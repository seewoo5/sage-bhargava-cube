from sage.all import *

from .binary_cf import *


class BhargavaCube(SageObject):
    """
    Bhargava cube.

    Follow the diagram (1) of the paper "Higher composition laws I: A new view on Gauss composition, and quadratic
    generalizations" by M. Bhargava for labeling:

    ```
        e ----- f
      / |     / |
    a ------ b  |
    |   |    |  |
    |   g ---|- h
    | /      | / 
    c ------ d
    ```

    Faces are labeled as:

    M_1 = [[a, b], [c, d]], N_1 = [[e, f], [g, h]]
    M_2 = [[a, c], [e, g]], N_2 = [[b, d], [f, h]]
    M_3 = [[a, e], [b, f]], N_3 = [[c, g], [d, h]]

    The corresponding quadratic forms are defined as

    Q_i = -det(x * M_i - y * N_i), i = 1, 2, 3.

    Note that some of the literatures (e.g. "Higher composition laws and applications" by M. Bhargava) uses

    Q_i = -det(x * M_i + y * N_i), i = 1, 2, 3

    instead, which are simply inverses each other.

    Also, we only deal with 'projective' cubes, i.e. the associated quadratic forms are all invertible.
    """

    def __init__(self, data=None):
        # Initialize with "identity" cube with discriminant 1.
        self._a, self._b, self._c, self._d, self._e, self._f, self._g, self._h = [1, 0, 0, 0, 0, 0, 0, 1]
        if isinstance(data, list):
            assert len(data) == 8, "You need 8 integers"
            self._a, self._b, self._c, self._d, self._e, self._f, self._g, self._h = [ZZ(x) for x in data]
        elif isinstance(data, BhargavaCube):
            for k in ["_a", "_b", "_c", "_d", "_e", "_f", "_g", "_h"]:
                setattr(self, k, getattr(data, k))
        elif isinstance(data, (list, tuple)) and len(data) == 2 and isinstance(data[0], BinaryQF) and isinstance(data[1], BinaryQF):
            # Initialize from two (primitive) binary quadratic forms
            self._from_bqf_pair(*data)
        elif isinstance(data, (list, tuple)) and len(data) == 3 and isinstance(data[0], BinaryQF) and isinstance(data[1], BinaryQF) and isinstance(data[2], BinaryQF):
            # Initialize from three (primitive) binary quadratic forms
            # with same discriminants and their composition is the identity in the class group
            self._from_bqf_triple(*data)
        elif isinstance(data, BinaryCF):
            # Initialize from a binary cubic form
            self._from_bcf(data)
        
    def _check_idx(self, i):
        assert i in [1, 2, 3], "Index out of range - i should be one of 1, 2, 3"

    def _check_projective(self):
        """Check if a given set of integers form a 'projective' cube, i.e. all Q_i's are primitive."""
        for i in [1, 2, 3]:
            assert self.Q(i).is_primitive(), "Q_" + str(i) + " is not primitive."

    def _from_bqf_pair(self, bqf1, bqf2):
        assert bqf1.is_primitive(), "First form is not primitive"
        assert bqf2.is_primitive(), "Second form is not primitive"
        assert bqf1[1] % 2 == 0, "b1 is not even"
        assert bqf2[1] % 2 == 0, "b2 is not even"
        a, b, c, d, e, f = bqf1[0], bqf1[1] / 2, bqf1[2], bqf2[0], bqf2[1] / 2, bqf2[2]
        self._a, self._b, self._c, self._d, self._e, self._f, self._g, self._h = [a, b, b, c, d, e, e, f]

    @staticmethod
    def from_bqf_pair(bqf1, bqf2):
        cb = BhargavaCube()
        cb._from_bqf_pair(bqf1, bqf2)
        return cb

    def _from_bqf_triple(self, bqf1, bqf2, bqf3):
        D = bqf1.discriminant()
        assert bqf1.is_primitive()
        assert bqf2.is_primitive()
        assert bqf3.is_primitive()
        assert (bqf1 * bqf2 * bqf3).reduced_form() == BinaryQF.principal(D)

        raise NotImplementedError
        # check primitive

    @staticmethod
    def from_bqf_triple(bqf1, bqf2, bqf3):
        cb = BhargavaCube()
        cb._from_bqf_triple(bqf1, bqf2, bqf3)
        return cb

    def _from_bcf(self, bcf):
        assert bcf._check_bc_div3()
        p, q, r, s = bcf[0], bcf[1] / 3, bcf[2] / 3, bcf[3]
        self._a, self._b, self._c, self._d, self._e, self._f, self._g, self._h = [p, q, q, r, q, r, r, s]

    def M(self, i):
        self._check_idx(i)
        if i == 1:
            return matrix([[self._a, self._b], [self._c, self._d]])
        elif i == 2:
            return matrix([[self._a, self._c], [self._e, self._g]])
        else:  # i == 3:
            return matrix([[self._a, self._e], [self._b, self._f]])

    def N(self, i):
        self._check_idx(i)
        if i == 1:
            return matrix([[self._e, self._f], [self._g, self._h]])
        elif i == 2:
            return matrix([[self._b, self._d], [self._f, self._h]])
        else:  # i == 3:
            return matrix([[self._c, self._g], [self._d, self._h]])

    def Q(self, i):
        x, y = ZZ['x,y']._first_ngens(2)
        self._check_idx(i)
        mat1 = x * self.M(i) - y * self.N(i)
        bqf = BinaryQF(-mat1.det())
        return bqf

    def discriminant(self):
        """Discriminant of a cube. Note that Q(i).discriminant() are all equal for i = 1, 2, 3."""
        return self.Q(1).discriminant()

    def matrices_action_left(self, triple):
        """
        Left ction of SL_2(Z) x SL_2(Z) x SL_2(Z).
        Following Bhargava's paper.
        """
        assert isinstance(triple, (list, tuple)) and len(triple) == 3
        mat1, mat2, mat3 = [matrix(ZZ, x) for x in triple]
        r1, s1, t1, u1 = mat1[0, 0], mat1[0, 1], mat1[1, 0], mat1[1, 1]
        r2, s2, t2, u2 = mat2[0, 0], mat2[0, 1], mat2[1, 0], mat2[1, 1]
        r3, s3, t3, u3 = mat3[0, 0], mat3[0, 1], mat3[1, 0], mat3[1, 1]

        res = BhargavaCube(self)

        # mat1
        M1_ = r1 * res.M(1) + s1 * res.N(1)
        N1_ = t1 * res.M(1) + u1 * res.N(1)
        res = BhargavaCube([M1_[0][0], M1_[0][1], M1_[1][0], M1_[1][1], N1_[0][0], N1_[0][1], N1_[1][0], N1_[1][1]])

        # mat2
        M2_ = r2 * res.M(2) + s2 * res.N(2)
        N2_ = t2 * res.M(2) + u2 * res.N(2)
        res = BhargavaCube([M2_[0][0], N2_[0][0], M2_[0][1], N2_[0][1], M2_[1][0], N2_[1][0], M2_[1][1], N2_[1][1]])

        # mat3
        M3_ = r3 * res.M(3) + s3 * res.N(3)
        N3_ = t3 * res.M(3) + u3 * res.N(3)
        res = BhargavaCube([M3_[0][0], M3_[1][0], N3_[0][0], N3_[1][0], M3_[0][1], M3_[1][1], N3_[0][1], N3_[1][1]])
        return res

    def matrices_action_right(self, triple):
        """
        Right action of SL_2(Z) x SL_2(Z) x SL_2(Z).
        Same as left action with transposed matrices.
        """
        assert isinstance(triple, (list, tuple)) and len(triple) == 3
        mat1, mat2, mat3 = [matrix(ZZ, x).transpose() for x in triple]
        return self.matrices_action_left((mat1, mat2, mat3))
        

    @staticmethod
    def id(D):
        """Identity cube for a given discriminant."""
        if D % 4 == 0:
            return BhargavaCube([0, 1, 1, 0, 1, 0, 0, D / 4])
        elif D % 4 == 1:
            return BhargavaCube([0, 1, 1, 1, 1, 1, 1, (D + 3) / 4])
        else:
            raise ValueError("D should be 0 or 1 modulo 4")

    def __mul__(self, other):
        """Composition of two cubes."""
        R1 = self.Q(1) * other.Q(1)
        R2 = self.Q(2) * other.Q(2)
        R3 = self.Q(3) * other.Q(3)
        return BhargavaCube.from_bqf_triple(R1, R2, R3)

    def __pow__(self, n):
        if n == 0:
            return BhargavaCube.id(self.discriminant())
        elif n > 0:
            if n == 1:
                return self
            else:
                res = BhargavaCube.id(self.discriminant())
                for _ in range(n):
                    res *= self
                return res
        else:
            return self.inverse() ** (-n)

    def inverse(self):
        """Inverse of a cube under the composition."""
        inv = BhargavaCube(self)
        inv._b *= (-1)
        inv._c *= (-1)
        inv._e *= (-1)
        inv._h *= (-1)
        return inv

    def __repr__(self):
        return f"BhargavaCube(a={self._a},b={self._b},c={self._c},d={self._d},e={self._e},f={self._f},g={self._g},h={self._h})"

    def __str__(self):
        return repr(self)
