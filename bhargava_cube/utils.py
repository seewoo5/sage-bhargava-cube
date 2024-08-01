from sage.all import *


def xgcd_(a, b=None):
    if b is not None:
        return xgcd(a, b)

    ls = a
    assert isinstance(ls, (tuple, list))
    assert len(ls) > 1
    if len(ls) == 2:
        return xgcd(ls[0], ls[1])
    else:
        xgcd_t = xgcd_(ls[1:])  # xgcd_t[0] = sum(xgcd_t[i] * ls[i], 1 \le i \le n-1)
        g, c_h, c_t = xgcd(ls[0], xgcd_t[0])  # g = c_h * ls[0] * c_t * xgcd_t[0]
        res = [g, c_h] + [c_t * c for c in xgcd_t[1:]]
        return tuple(res)


def quad_ring(D):
    """Quadratic ring of discriminant D with its generator"""
    eps = D % 4
    assert eps in [0, 1]
    R0 = ZZ['t']
    t = R0.gens()[0]
    I = R0.ideal(t ** 2 - eps * t - (D - eps) / 4)
    R = QuotientRing(R0, I)
    return R, t


def trace(x, D):
    """Trace of an element in a quadratic ring of disriminant D"""
    a, b = x[0], x[1]
    if D % 4 == 0:
        return 2 * a
    return 2 * a + b


def conj(x, D):
    """Conjugation of an element in a quadratic ring of discriminant D"""
    return trace(x, D) - x


def norm(x, D):
    """Norm of an element in a quadratic ring of discriminant D"""
    nx = x * conj(x, D)
    return ZZ(nx[0])
