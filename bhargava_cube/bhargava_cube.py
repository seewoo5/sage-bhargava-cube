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

    def is_projective(self):
        """Check if a given set of integers form a 'projective' cube, i.e. all Q_i's are primitive."""
        return self.Q(1).is_primitive() and self.Q(2).is_primitive() and self.Q(3).is_primitive()

    def _check_projective(self):
        assert self.is_projective()

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
        """Reconstruct a cube that gives three given (primitive) binary quadratic forms
        whose composition is an identity class.
        Based on the article "Composition and Bhargava's Cubes" by Florian Bouyer.
        """
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
        The triple (gamma_1, gamma_2, gamma_3) with gamma_i = [[r_i, s_i], [t_i, u_i]] acts as

        (M_i, N_i) -> (r_i * M_i + s_i * N_i, t_i * M_i, u_i * N_i)

        which is equivalent to

        (M_{i-1}, N_{i-1}) -> (M_{i-1} * gamam_i^T, N_{i-1} * gamma_i^T)

        or

        (M_{i+1}, N_{i+1}) -> (gamma_i * M_{i+1}, gamma_i * N_{i+1})


        with i \in {1, 2, 3}, index modulo 3.

        Following Bhargava's paper. Note that the action of gamma_i's commute each other.
        """
        assert isinstance(triple, (list, tuple)) and len(triple) == 3
        return self.matrices_action_right([matrix(ZZ, x).transpose() for x in triple])

    def matrices_action_right(self, triple):
        """
        Right action of SL_2(Z) x SL_2(Z) x SL_2(Z). Same as the left action with transposed matrices.

        The triple (gamma_1, gamma_2, gamma_3) with gamma_i = [[r_i, s_i], [t_i, u_i]] acts as

        (M_i, N_i) -> (r_i * M_i + t_i * N_i, s_i * M_i, u_i * N_i)

        which is equivalent to

        (M_{i-1}, N_{i-1}) -> (M_{i-1} * gamam_i, N_{i-1} * gamma_i)

        or

        (M_{i+1}, N_{i+1}) -> (gamma_i^T * M_{i+1}, gamma_i^T * N_{i+1})

        with i \in {1, 2, 3}, index modulo 3.

        Also Florian Bouyer's article "Composition and Bhargava's Cubes" uses this right action.
        """
        assert isinstance(triple, (list, tuple)) and len(triple) == 3
        gamma1, gamma2, gamma3 = [matrix(ZZ, x) for x in triple]

        res = BhargavaCube(self)

        # gamma1
        M3_, N3_ = res.M(3) * gamma1, res.N(3) * gamma1
        data = [M3_[0][0], M3_[1][0], N3_[0][0], N3_[1][0], M3_[0][1], M3_[1][1], N3_[0][1], N3_[1][1]]
        res = BhargavaCube(data)
        # gamma2
        M1_, N1_ = res.M(1) * gamma2, res.N(1) * gamma2
        data = M1_.list() + N1_.list()
        res = BhargavaCube(data)
        # gamma3
        M2_, N2_ = res.M(2) * gamma3, res.N(2) * gamma3
        data = [M2_[0][0], N2_[0][0], M2_[0][1], N2_[0][1], M2_[1][0], N2_[1][0], M2_[1][1], N2_[1][1]]
        res = BhargavaCube(data)
        return res

    def normal_form(self):
        """
        Transform a projective cube into an equivalent cube of normal form, i.e. a = 1 and b = c = e = 0.

        ```
            0 ----- f
          / |     / |
        1 ------ 0  |
        |   |    |  |
        |   g ---|- h
        | /      | / 
        0 ------ d
        ```

        Use Smith normal form and left/right actions of SL_2^3.
        """
        if self.discriminant() == 0:
            raise ValueError("Discriminant should be nonzero")
        if not self.is_projective():
            raise ValueError("Cube is not projective")

        res = BhargavaCube(self)
        I = matrix([[1, 0], [0, 1]])
        I2 = matrix([[1, 0], [0, -1]])

        # M1
        _, U1, V1 = res.M(1).smith_form()  # U1 * M1 * V1 = D1
        if U1.det() == -1:
            U1 = I2 * U1
        if V1.det() == -1:
            V1 = V1 * I2
        res = res.matrices_action_left((I, I, U1)).matrices_action_right((I, V1, I))

        # M2
        _, U2, V2 = res.M(2).smith_form()  # U2 * M2 * V2 = D2
        if U2.det() == -1:
            U2 = I2 * U2
        if V2.det() == -1:
            V2 = V2 * I2
        res = res.matrices_action_left((U2, I, I)).matrices_action_right((I, I, V2))

        # M3
        _, U3, V3 = res.M(3).smith_form()  # U3 * M3 * V3 = D3
        if U3.det() == -1:
            U3 = I2 * U3
        if V3.det() == -1:
            V3 = V3 * I2
        res = res.matrices_action_left((I, U3, I)).matrices_action_right((V3, I, I))

        assert res._a == 1 and res._b == 0 and res._c == 0 and res._e == 0, "Failed to normalize"
        return res

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
        # TODO: Make faster using the class group order when D < 0
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

    def show(self):
        """
        Show as 3D cube.
        Based on this answer: https://ask.sagemath.org/question/63031/how-can-we-label-3d-cube/?answer=63035#post-id-63035
        """
        v_opt = dict(fontsize="200%", fontstyle="italic", color="blue")
        f_opt = dict(fontsize="200%", fontstyle="italic", color="black")

        fig = cube(center=(0.5,0.5,0.5), size=1, color="white", frame_thickness=2, frame_color="black", opacity=0.2, threejs_flat_shading=True)
        fig += (text3d(f"c={self._c}", (1.02,0,0), **v_opt) + text3d(f"d={self._d}", (1.02,1.02,0), **v_opt)
                + text3d(f"b={self._b}", (1.02,1.02,1.02), **v_opt) + text3d(f"a={self._a}", (1.02,0,1.02), **v_opt)
                + text3d(f"g={self._g}", (-0.02,0,0), **v_opt) + text3d(f"h={self._h}", (-0.02,1.02,0), **v_opt)
                + text3d(f"f={self._f}", (-0.02,1.02,1.02), **v_opt) + text3d(f"e={self._e}", (-0.02,0,1.02), **v_opt))
        # TODO: fix text orientation on faces
        fig += (text3d("M1", (1.05,0.5,0.5),**f_opt) + text3d("N1", (-0.05,0.5,0.5),**f_opt)
                + text3d("M2", (0.5,-0.05,0.5),**f_opt) + text3d("N2", (0.5,1.05,0.5),**f_opt)
                + text3d("M3", (0.5,0.5,1.05),**f_opt) + text3d("N3", (0.5,0.5,-0.05),**f_opt))
        show(fig, frame=False)
