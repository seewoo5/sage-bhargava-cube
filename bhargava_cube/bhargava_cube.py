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

    Q_i = -det(x * M_i + y * N_i), i = 1, 2, 3.

    Note that some of the literatures, including the Bharagava's original paper uses

    Q_i = -det(x * M_i - y * N_i), i = 1, 2, 3

    instead, which are simply inverses each other.
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
        elif isinstance(data, BinaryCF):
            # Initialize from a binary cubic form
            self._from_bcf(data)
        
    def _check_idx(self, i):
        assert i in [1, 2, 3], "Index out of range - i should be one of 1, 2, 3"

    def is_projective(self):
        """Check if a given set of integers form a 'projective' cube, i.e. all Q_i's are primitive."""
        return self.Q(1).is_primitive() and self.Q(2).is_primitive() and self.Q(3).is_primitive()

    def is_normal(self):
        return self._b == 0 and self._c == 0 and self._e == 0

    def _check_projective(self):
        assert self.is_projective()

    def _from_bqf_pair(self, bqf1, bqf2):
        """
        For given two (primitive) binary quadratic forms `bqf1` and `bqf2`
        of same discriminant, return a cube `c` with bqf1 = c.Q(1), bqf2 = c.Q(2).
        Based on the Theorem 3.7 of the article "Composition and Bhargava's Cubes"
        by Florian Bouyer.
        """
        D = bqf1.discriminant()
        assert D != 0
        assert bqf2.discriminant() == D
        assert bqf1.is_primitive()
        assert bqf2.is_primitive()

        bqf1 = bqf1.reduced_form()
        bqf2 = bqf2.reduced_form()
        a, b, c = bqf1[0], bqf1[1], bqf1[2]
        a_, b_, c_ = bqf2[0], bqf2[1], bqf2[2]
        assert a * a_ != 0, "Both a and a' should be nonzero"
        
        e = gcd([a, a_, (b + b_) / 2])
        R = IntegerModRing(a)
        m_ = matrix(R, [[(b + b_) / 2], [a_]])
        v_ = vector(R, [-e * c_, e * (b - b_) / 2])
        f = ZZ(m_.solve_right(v_)[0])
        g = (-(b - b_) * e / 2 + a_ * f) / a
        h = (-(b + b_) * f / 2 - c_ * e) / a
        res = BhargavaCube([0, -a / e, -e, f, -a_ / e, (b + b_) / (-2 * e), g, -h])
        assert res.is_projective()
        return res

    @staticmethod
    def from_bqf_pair(bqf1, bqf2):
        cb = BhargavaCube()
        return cb._from_bqf_pair(bqf1, bqf2)

    def _from_bcf(self, bcf):
        assert bcf.is_bc_div3()
        p, q, r, s = bcf[0], bcf[1] // 3, bcf[2] // 3, bcf[3]
        self._a, self._b, self._c, self._d, self._e, self._f, self._g, self._h = [p, q, q, r, q, r, r, s]

    @staticmethod
    def from_bcf(bcf):
        cb = BhargavaCube()
        return cb._from_bcf(bcf)

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
        """
        Associated binary quadratic forms,

        Q_i(x, y) = -det(x * M_i + y * N_i)

        for i = 1, 2, 3.
        """
        x, y = ZZ['x,y']._first_ngens(2)
        self._check_idx(i)
        mat1 = x * self.M(i) + y * self.N(i)
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
        Note that normal form is not unique, and numbers can be large.
        TODO: Small numbers.
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
        assert res.is_normal(), "Failed to normalize"
        return res
    
    def is_reduced(self):
        """Check if a cube is 'reduced', i.e. all the associated binary cubic forms Q_i are reduced."""
        return self.Q(1).is_reduced() and self.Q(2).is_reduced() and self.Q(3).is_reduced()

    def reduced_form(self):
        """
        Return a reduced form of a cube.
        """
        _, t1 = self.Q(1).reduced_form(transformation=True)
        _, t2 = self.Q(2).reduced_form(transformation=True)
        _, t3 = self.Q(3).reduced_form(transformation=True)
        return self.matrices_action_right((t1, t2, t3))

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
        """
        Composition of two cubes.
        Based on the article "Composition and Bhargava's Cubes" by Florian Bouyer.
        """
        cs = self.normal_form()
        co = other.normal_form()
        D = cs.discriminant()
        assert D == other.discriminant()

        Qs1, Qs2 = cs.Q(1), cs.Q(2)
        Qo1, Qo2 = co.Q(1), co.Q(2)


        # When the associated binary quadratic forms are not negative definite
        if not Qs1.is_negdef() and not Qs2.is_negdef() and not Qs2.is_negdef() and not Qo2.is_negdef():
            R1 = Qs1 * Qo1
            R2 = Qs2 * Qo2
            return BhargavaCube.from_bqf_pair(R1, R2)

        # When the associated binary quadratic forms are negative definite
        # Use Dirichlet's composition
        d, g, h = cs._d, cs._g, cs._h
        d_, g_, h_ = co._d, co._g, co._h

        e1 = gcd([d, d_, (h + h_) / 2])
        e2 = gcd([g, g_, (h + h_) / 2])

        mB1, mB2 = 2 * d / e1, 2 * d_ / e1
        mB3 = lcm(mB1, mB2)
        mB4 = mB1 * mB2 / mB3
        B1_ = crt([h, h_], [mB1, mB2])  # solution mod mB3
        for l in range(mB4):
            if ((B1_ + l * mB3) ** 2 - D) % (mB1 * mB2) == 0:
                B1 = B1_ + l * mB3
                break

        mB1_, mB2_ = 2 * g / e2, 2 * g_ / e2
        mB3_ = lcm(mB1_, mB2_)
        mB4_ = mB1_ * mB2_ / mB3_
        B2_ = crt([h, h_], [mB1_, mB2_])  # solution mod mB3_
        for l in range(mB4_):
            if ((B2_ + l * mB3_) ** 2 - D) % (mB1_ * mB2_) == 0:
                B2 = B2_ + l * mB3_
                break

        R1 = BinaryQF(ZZ(d * d_ / (e1 ** 2)), ZZ(B1), ZZ((e1 ** 2) * (B1 ** 2 - D) / (4 * d * d_)))
        R2 = BinaryQF(ZZ(g * g_ / (e2 ** 2)), ZZ(B2), ZZ((e2 ** 2) * (B2 ** 2 - D) / (4 * g * g_)))
        return BhargavaCube.from_bqf_pair(R1, R2)

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
