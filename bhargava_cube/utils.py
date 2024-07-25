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
