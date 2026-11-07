"""Referee cross-check (float, NOT rigorous) of the size of the Lemma-A bound at true scale.

Evaluates, independently of the phase2 code,
   B_A(L, eps) = L^2/U + (eps X/e)^eps (zeta(1+eps) * Tq - 1),
   Tq = Delta^{-2} sum_{n<V} n^{-s} H(n)^2,  H(n) = M(V/n) - M(U/n),
with the sum over n > 1e5 replaced by the (very accurate at this scale) integral, M(y) exact (float table)
for y <= 1e6 and M(y) = A + B log y beyond (|R| <~ 1e-5 there).  This is the *true value* of the expression
that lemmaA_d4.py bounds rigorously, so the rigorous output should be slightly above it.
"""
import math, sys, json
import numpy as np
import mpmath as mp


def mobius(N):
    mu = np.ones(N + 1, dtype=np.int64); mu[0] = 0
    isp = np.ones(N + 1, dtype=bool); isp[:2] = False
    for p in range(2, int(N ** 0.5) + 1):
        if isp[p]:
            isp[p * p::p] = False
    for p in np.nonzero(isp)[0]:
        p = int(p); mu[p::p] *= -1
        if p * p <= N:
            mu[p * p::p * p] = 0
    return mu

Y0 = 10**6
MU = mobius(Y0)
GLx, GLw = np.polynomial.legendre.leggauss(4)


def setup(eps):
    s = 1 + eps
    z = float(mp.zeta(s)); zp = float(mp.zeta(s, derivative=1))
    B = 1 / z; A = -zp / z ** 2
    k = np.arange(1, Y0 + 1, dtype=float); m = MU[1:].astype(float)
    P = np.cumsum(m * k ** (-s)); Q = np.cumsum(m * k ** (-s) * np.log(k))
    return s, z, A, B, P, Q


def piecewise_int(eps, P, Q, a_const, b_coef_minus, sign):
    """sum_k int_{log k}^{log(k+1)} e^{eps l} (a_const + sign*(Q_k - P_k l) + b_coef_minus*l)^2 dl, k=1..Y0-1
    i.e. integrand (c + d l)^2 with c = a_const + sign*Q_k, d = b_coef_minus - sign*P_k."""
    k = np.arange(1, Y0, dtype=float)
    l0 = np.log(k); l1 = np.log(k + 1)
    c = a_const + sign * Q[:-1]; d = b_coef_minus - sign * P[:-1]
    tot = 0.0
    for x, w in zip(GLx, GLw):
        l = 0.5 * (l0 + l1) + 0.5 * (l1 - l0) * x
        tot += float(np.sum(w * 0.5 * (l1 - l0) * np.exp(eps * l) * (c + d * l) ** 2))
    return tot


def quad_exp_poly(eps, la, lb, c, d, n=2000):
    l = np.linspace(la, lb, n + 1)
    f = np.exp(eps * l) * (c + d * l) ** 2
    return float(np.trapezoid(f, l))


def Tq(u, v, L, eps, cache={}):
    if eps not in cache:
        cache[eps] = setup(eps)
    s, z, A, B, P, Q = cache[eps]
    lU = u * L; lV = v * L; D = lV - lU
    N1 = 10**5
    # region 0: n <= N1, H = B*Delta (R terms ~ 0 since U/n >= e^{lU}/1e5 is huge)
    n = np.arange(1, N1 + 1, dtype=float)
    r0 = float(np.sum(n ** (-s))) * B ** 2
    # region I: N1 < n <= U, y = U/n in [1, U/N1]; H = A + B(D + log y) - M(y)
    #   y <= Y0: M(y) = P_k log y - Q_k  ->  H = (A + B D + Q_k) + (B - P_k) l
    rI = math.exp(-eps * lU) * piecewise_int(eps, P, Q, A + B * D, B, +1) / D ** 2
    #   y in [Y0, U/N1]: H = B D
    lmax = lU - math.log(N1)
    rI += math.exp(-eps * lU) * B ** 2 * (math.exp(eps * lmax) - math.exp(eps * math.log(Y0))) / eps
    # region II: U < n < V, y = V/n in [1, e^D]; H = M(y)
    rII = math.exp(-eps * lV) * piecewise_int(eps, P, Q, 0.0, 0.0, -1) / D ** 2
    rII += math.exp(-eps * lV) * quad_exp_poly(eps, math.log(Y0), D, A, B) / D ** 2
    return z, r0 + rI + rII, (r0, rI, rII)


def bound(u, v, x, L, a):
    eps = a / (x * L)
    z, T, parts = Tq(u, v, L, eps)
    lX = x * L
    rank = math.exp(eps * lX) * (eps / math.e) ** eps
    return L ** 2 / math.exp(u * L) + rank * (z * T - 1), z * T, parts


if __name__ == "__main__":
    rows = [(28.7290, 29.0, 2.1781287, 4.4744028, 7.0798370)]
    if len(sys.argv) > 1:
        rows = json.loads(sys.argv[1])
    for (L0, L1, u, v, x) in rows:
        for L in (L0, L1):
            best = None
            for a in (1.8, 2.05, 2.3):
                b, zT, parts = bound(u, v, x, L, a)
                print(f"  row u={u} v={v} x={x} L={L:.4f} a={a}: bound={b:.4f}  zeta*Tq={zT:.6f} parts={tuple(round(p,6) for p in parts)}")
                best = b if best is None else min(best, b)
            print(f" => L={L:.4f}: float value of Lemma-A expression (best a) = {best:.4f}")
        sys.stdout.flush()
