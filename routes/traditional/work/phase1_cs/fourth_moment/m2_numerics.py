# -*- coding: utf-8 -*-
"""
(A) RIGOROUS enclosures of M_2(0,3000) and M_2(3000,6000), M_2(A,B)=int_A^B |zeta(1/2+it)|^4 dt.
    Taylor models: on each panel [t_k-h, t_k+h], F(t)=zeta(1/2+it)^2 zeta(1/2-it)^2 (= |zeta|^4 on R)
    F(t_k+tau) = sum_{n<N} c_n(t_k) tau^n + c_N(xi) tau^N  (Lagrange, xi real in the panel),
    c_N(xi) enclosed by evaluating the Taylor coefficients on the real ball [t_k-h,t_k+h]
    (acb_series.zeta).  int_{-h}^{h} = sum_{n even<N} c_n 2h^{n+1}/(n+1) + [+-] sup|c_N| 2h^{N+1}/(N+1).
(B) NON-RIGOROUS (float, Gauss-Legendre) values of M_2(T) up to T=2e4 and comparison with
    the paper's bounds and with T P_4(log(T/2pi)).
Run: python -I m2_numerics.py [A|B|AB]
"""
import sys, time, math
from flint import arb, acb, acb_series, ctx

I = acb(0, 1)


def panel(tk, h, N):
    """rigorous enclosure (arb) of int_{tk-h}^{tk+h} |zeta(1/2+it)|^4 dt"""
    ctx.cap = N + 1
    s1 = acb_series([acb(0.5, tk), I])
    s2 = acb_series([acb(0.5, -tk), -I])
    F = (acb_series.zeta(s1) * acb_series.zeta(s2)) ** 2
    c = F.coeffs()
    tot = arb(0)
    hh = arb(h)
    for n in range(0, N, 2):
        tot += c[n].real * 2 * hh ** (n + 1) / (n + 1)
    tb = arb(tk, h)
    b1 = acb_series([acb(0.5, 0) + I * tb, I])
    b2 = acb_series([acb(0.5, 0) - I * tb, -I])
    Fb = (acb_series.zeta(b1) * acb_series.zeta(b2)) ** 2
    cN = abs(Fb.coeffs()[N])
    err = cN * 2 * hh ** (N + 1) / (N + 1)
    # imaginary parts of c_n vanish on R (F real on R); only real parts integrated
    return tot + arb(0, (err.mid() + err.rad()))


def rigorous_M2(a, b, h, N, prec=64, report=None):
    ctx.prec = prec
    npan = int(round((b - a) / (2 * h)))
    assert abs(npan * 2 * h - (b - a)) < 1e-9
    tot = arb(0)
    t0 = time.time()
    for k in range(npan):
        tk = arb(a) + arb(2 * h) * k + arb(h)   # exact binary if h is a dyadic number
        tot += panel(tk, h, N)
        if report and (k + 1) % report == 0:
            print("    ... t=%.1f  partial=%s  (%.0fs)" % (float(tk.mid()) + h, tot.str(10, radius=True), time.time() - t0), flush=True)
    return tot


def gl_nodes(m):
    import numpy as np
    x, w = np.polynomial.legendre.leggauss(m)
    return x, w


def float_M2(Tlist, step=0.125, m=8):
    """non-rigorous: composite Gauss-Legendre with flint zeta at 53 bits"""
    ctx.prec = 53
    x, w = gl_nodes(m)
    out = {}
    Tmax = max(Tlist)
    acc = 0.0
    t = 0.0
    Ts = sorted(Tlist)
    j = 0
    while t < Tmax - 1e-12:
        a, b = t, t + step
        mid, half = (a + b) / 2, (b - a) / 2
        s = 0.0
        for xi, wi in zip(x, w):
            z = acb(0.5, mid + half * xi).zeta()
            v = float(abs(z).mid())
            s += wi * v ** 4
        acc += s * half
        t = b
        while j < len(Ts) and abs(t - Ts[j]) < 1e-9:
            out[Ts[j]] = acc
            j += 1
    return out


P2C = [1.312424385961669226168440066229978, 3.227907964901254764380689851274668,
       2.425962198846682004756575310160663, 0.69886988487897996984709628427658502,
       0.0506605918211688857219397316048638]   # CFKRS (math/0206018v3) eq. (5.1.5), coeffs of x^0..x^4


def intP2(T):
    """int_0^T P2(log(t/2pi)) dt = 2pi int_0^X P2(log u) du, X=T/2pi  (CFKRS (2.7.2); for k=2 this is
    Heath-Brown's theorem, error O(T^{7/8+eps}), improved to O(T^{2/3+eps}) by Ivic-Motohashi)."""
    X = T / (2 * math.pi)
    l = math.log(X)
    tot = 0.0
    for k, ck in enumerate(P2C):
        # int_0^X (log u)^k du = X sum_{j=0}^k (-1)^{k-j} k!/j! l^j
        tot += ck * X * sum((-1) ** (k - j) * math.factorial(k) / math.factorial(j) * l ** j for j in range(k + 1))
    return 2 * math.pi * tot


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "AB"
    if "A" in mode:
        print("(A) RIGOROUS Taylor-model integration, h=1/8 (panel length 1/4), N=22, prec=64")
        t = time.time()
        A1 = rigorous_M2(0, 3000, 0.125, 22, 64, report=3000)
        print("  M2(0,3000)    in %s   (%.0fs)" % (A1.str(12, radius=True), time.time() - t))
        print("    paper: 7.031e5 < M2(3e3) < 7.032e5 :", (A1 > 703100) and (A1 < 703200))
        t = time.time()
        A2 = rigorous_M2(3000, 6000, 0.125, 22, 64, report=3000)
        print("  M2(3000,6000) in %s   (%.0fs)" % (A2.str(12, radius=True), time.time() - t))
        print("    paper: 1.249e6 < M2(3e3,6e3) < 1.25e6 :", (A2 > 1249000) and (A2 < 1250000))
    if "B" in mode:
        print("(B) NON-RIGOROUS float values (composite Gauss-Legendre, step 1/8, 8 nodes)")
        Ts = [3000.0, 5000.0, 6000.0, 10000.0, 20000.0]
        t = time.time()
        V = float_M2(Ts)
        print("  (%.0fs)" % (time.time() - t))
        pi2 = math.pi ** 2
        for T in Ts:
            x = math.log(T / (2 * math.pi))
            cs1 = T / pi2 * math.log(T / 2) ** 4 + 20.7225 * T * math.log(T / 2) ** 3.5 + 1.9532e6
            cs2 = T / (2 * pi2) * math.log(T / 2) ** 4 + 59.3 * T * math.log(T / 2) ** 3 + 1.3796e9
            print("  T=%7.0f  M2(T)~%.7e  int_0^T P2=%.7e  diff=%.3e  CS(main4thPM1) bound=%.4e  CS(row1e4) bound=%.4e"
                  % (T, V[T], intP2(T), V[T] - intP2(T), cs1, cs2 if T >= 1e4 else float('nan')))
        print("  M2(1e4,2e4) ~ %.6e  (paper bound 9.9857e8);  M2(1e4) ~ %.6e (paper bound 3.8095e8)"
              % (V[20000.0] - V[10000.0], V[10000.0]))
        print("  M2(3e3,6e3) ~ %.6e ; M2(3e3) ~ %.6e" % (V[6000.0] - V[3000.0], V[3000.0]))
