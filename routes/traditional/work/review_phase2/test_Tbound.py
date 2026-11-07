"""Referee test of lemmaA_d4.T_bound (the code under review) against an exact float64 evaluation of
      Tq(L) := Delta^{-2} sum_{n<V} n^{-s} H(n)^2,  H(n) = M(V/n) - M(U/n)
at moderate scale (U ~ 5e3, V ~ 5e6), where the exact sum is computable.  T_bound must be >= Tq(L) for every
L in [La, Lb].  Also reports the tightness.  (Exploration / referee check; not a claimed bound.)
"""
import math, sys, os
import numpy as np
sys.path.insert(0, r"D:\UGit\AI4Math\legendre_k67\work\phase2_lemmas")
import lemmaA_d4 as A
from flint import arb


def mobius(N):
    mu = np.ones(N + 1, dtype=np.int64); mu[0] = 0
    isp = np.ones(N + 1, dtype=bool); isp[:2] = False
    for p in range(2, int(N ** 0.5) + 1):
        if isp[p]:
            isp[p * p::p] = False
    for p in np.nonzero(isp)[0]:
        p = int(p)
        mu[p::p] *= -1
        if p * p <= N:
            mu[p * p::p * p] = 0
    return mu


def exact_T(u, v, L, eps, mu):
    U = math.exp(u * L); V = math.exp(v * L); D = (v - u) * L
    Vi = int(math.floor(V))
    if V == Vi:
        Vi -= 1
    s = 1 + eps
    kk = np.arange(1, Vi + 1, dtype=float)
    m = mu[1:Vi + 1].astype(float)
    P = np.cumsum(m * kk ** (-s)); Q = np.cumsum(m * kk ** (-s) * np.log(kk))
    def M(y):
        out = np.zeros_like(y)
        msk = y >= 1
        idx = np.floor(y[msk]).astype(np.int64) - 1
        out[msk] = P[idx] * np.log(y[msk]) - Q[idx]
        return out
    n = kk
    H = M(V / n) - M(U / n)
    return float(np.sum(n ** (-s) * H ** 2)) / D ** 2


if __name__ == "__main__" and len(sys.argv) == 1:
    Y0 = 500; N1 = 10
    La, Lb = 10.0, 10.25
    u = math.log(5100) / 10; v = (math.log(5100) + 7.0) / 10
    us, vs = f"{u:.10f}", f"{v:.10f}"
    Vmax = int(math.exp(float(vs) * Lb)) + 2
    mu = mobius(Vmax)
    print(f"u={us} v={vs}  U in [{math.exp(float(us)*La):.0f},{math.exp(float(us)*Lb):.0f}]  V up to {Vmax}")
    for eps in ("0.01", "0.03", "0.06", "0.1"):
        D = A.M1Data(eps, Y0=Y0)
        # uniform bound over the piece, and pointwise bounds
        Tb, parts = A.T_bound(D, arb(us), arb(vs), arb(La), arb(Lb), N1=N1)
        Tb = A.f_up(Tb)
        ex = [exact_T(float(us), float(vs), L, float(eps), mu) for L in (La, 0.5 * (La + Lb), Lb)]
        Tp = A.f_up(A.T_bound(D, arb(us), arb(vs), arb(La), arb(La), N1=N1)[0])
        exa = ex[0]
        print(f"eps={eps}: T_bound[La,Lb]={Tb:.6f}  exact at La,mid,Lb = {ex[0]:.6f},{ex[1]:.6f},{ex[2]:.6f}  "
              f"{'OK' if Tb >= max(ex) else 'VIOLATED'} | point L=La: bound {Tp:.6f} vs exact {exa:.6f} "
              f"ratio {Tp/exa:.4f} {'OK' if Tp >= exa else 'VIOLATED'}")
        sys.stdout.flush()


def tight_rbar_factory(D, mu, Ymax):
    """non-rigorous: exact sup_{y in [e^l, Ymax]} |R(y)| from the float table (for a tightness test only)."""
    s = 1 + float(D.eps); A_ = float(D.A.mid()); B_ = float(D.B.mid())
    kk = np.arange(1, Ymax + 1, dtype=float); m = mu[1:Ymax + 1].astype(float)
    P = np.cumsum(m * kk ** (-s)); Q = np.cumsum(m * kk ** (-s) * np.log(kk))
    R_left = (P - B_) * np.log(kk) - Q - A_            # R(k)
    R_right = (P - B_) * np.log(kk + 1) - Q - A_       # R((k+1)^-)
    Rm = np.maximum(np.abs(R_left), np.abs(R_right))
    suf = np.maximum.accumulate(Rm[::-1])[::-1]       # suf[k-1] = max over [k, Ymax]
    def rbar(ly_lo):
        y = math.exp(float(arb(ly_lo).lower()))
        k = max(1, int(math.floor(y)))
        if k > Ymax:
            return arb(0)
        return arb(float(suf[k - 1]) * 1.0000001)
    return rbar


def tightness_run():
    Y0 = 500; N1 = 10
    La = Lb = 10.0
    u = math.log(5100) / 10; v = (math.log(5100) + 7.0) / 10
    us, vs = f"{u:.10f}", f"{v:.10f}"
    Vmax = int(math.exp(float(vs) * Lb)) + 2
    mu = mobius(Vmax)
    for eps in ("0.01", "0.03", "0.06", "0.1"):
        D = A.M1Data(eps, Y0=Y0)
        D.rbar = tight_rbar_factory(D, mu, Vmax)
        Tb, parts = A.T_bound(D, arb(us), arb(vs), arb(La), arb(Lb), N1=N1)
        ex = exact_T(float(us), float(vs), La, float(eps), mu)
        print(f"[tight R] eps={eps}: T_bound={A.f_up(Tb):.6f} exact={ex:.6f} ratio={A.f_up(Tb)/ex:.4f}  parts:",
              {k: round(A.f_up(x), 5) for k, x in parts.items()})
        sys.stdout.flush()


if __name__ == "__main__" and len(sys.argv) > 1 and sys.argv[1] == "tight":
    tightness_run()


def tightness_run2(Y0=20, N1=10_000, U0=2.1e5, Dl=3.5, L=12.0):
    u = math.log(U0) / L; v = (math.log(U0) + Dl) / L
    us, vs = f"{u:.10f}", f"{v:.10f}"
    Vmax = int(math.exp(float(vs) * L)) + 2
    mu = mobius(Vmax)
    for eps in ("0.01", "0.03", "0.06", "0.1"):
        D = A.M1Data(eps, Y0=Y0)
        Tr = A.f_up(A.T_bound(D, arb(us), arb(vs), arb(L), arb(L), N1=N1)[0])
        D.rbar = tight_rbar_factory(D, mu, Vmax)
        Tb, parts = A.T_bound(D, arb(us), arb(vs), arb(L), arb(L), N1=N1)
        ex = exact_T(float(us), float(vs), L, float(eps), mu)
        print(f"[Y0={Y0},N1={N1}] eps={eps}: exact={ex:.6f}  T_bound(RZA R)={Tr:.6f} ratio {Tr/ex:.4f} | "
              f"T_bound(tight R)={A.f_up(Tb):.6f} ratio={A.f_up(Tb)/ex:.4f}",
              {k: round(A.f_up(x), 5) for k, x in parts.items()})
        sys.stdout.flush()


if __name__ == "__main__" and len(sys.argv) > 1 and sys.argv[1] == "tight2":
    tightness_run2()
