"""Independent referee check of Lemma A at small scale (float64, exact Moebius values; NOT rigorous).

For U small, V = U^t, X = (UV)^c, Y = U/L^2 (L chosen), compute
  S      = sum_n Psi(n)^2/n (e^{-n/X} - e^{-n/Y})                         (brute force)
  ZQ(s)  = sum_n Psi(n)^2 n^{-s} = zeta(s) * sum_{d,e} psi_d psi_e [d,e]^{-s}  (exact double sum)
  RHS(s) = zeta(s)/Delta^2 * sum_{n<V} H(n)^2 n^{-s},  H(n) = M(V/n) - M(U/n)
and check (A1): ZQ <= RHS, and (A2): S <= L^2/U + (eps X/e)^eps (ZQ - 1).
Written from scratch; does not import the phase2 code.
"""
import math, sys
import numpy as np
from mpmath import zeta as mzeta


def mobius(N):
    mu = np.ones(N + 1, dtype=np.int64)
    mu[0] = 0
    isp = np.ones(N + 1, dtype=bool); isp[:2] = False
    for p in range(2, N + 1):
        if isp[p]:
            isp[2 * p::p] = False
            mu[p::p] *= -1
            if p * p <= N:
                mu[p * p::p * p] = 0
    return mu


def run(U, t, c, L, eps_list):
    V = U ** t
    X = (U * V) ** c
    Y = U / L ** 2
    assert Y < X
    Delta = math.log(V / U)
    Vi = int(math.floor(V))
    N = int(45 * X)
    mu = mobius(Vi)
    # psi_d exactly as Bellotti (3.1)
    def psi(d):
        if d <= U:
            return float(mu[d])
        if d <= V:
            return mu[d] * math.log(V / d) / Delta
        return 0.0
    ds = np.array([d for d in range(1, Vi + 1) if mu[d] != 0], dtype=np.int64)
    ps = np.array([psi(int(d)) for d in ds])
    # brute force S in chunks
    S = 0.0; S_noY = 0.0
    CH = 5_000_000
    Psi_small = None
    for a in range(1, N + 1, CH):
        b = min(N, a + CH - 1)
        arr = np.zeros(b - a + 1)
        for d, p in zip(ds, ps):
            first = ((a + d - 1) // d) * d
            if first > b:
                continue
            arr[first - a::d] += p
        n = np.arange(a, b + 1, dtype=float)
        S += float(np.sum(arr ** 2 / n * (np.exp(-n / X) - np.exp(-n / Y))))
        if a == 1:
            Psi_small = arr[:min(len(arr), 2000)].copy()
        S2_direct = (S2_direct if a > 1 else 0.0) + float(np.sum(arr ** 2 * n ** (-2.0)))
    # check Psi(n)=0 for 2<=n<=U, Psi(1)=1
    k = int(math.floor(U))
    assert abs(Psi_small[0] - 1) < 1e-12 and np.max(np.abs(Psi_small[1:k])) < 1e-9, "Psi(n)!=0 for n<=U"
    # M(y) table
    musV = mu[1:Vi + 1].astype(float)
    Q2 = 0.0
    for i in range(len(ds)):
        g = np.gcd(ds[i], ds); lcm = (ds[i] // g) * ds
        Q2 += ps[i] * float(np.sum(ps * lcm.astype(float) ** (-2.0)))
    print(f"   check of double-sum code at s=2: zeta(2)Q = {float(mzeta(2))*Q2:.10f}, direct sum_n<=N = {S2_direct:.10f}")
    out = []
    for eps in eps_list:
        s = 1 + eps
        z = float(mzeta(s))
        # exact double sum Q = sum psi_d psi_e [d,e]^{-s}
        Q = 0.0
        for i in range(len(ds)):
            d = ds[i]
            g = np.gcd(d, ds)
            lcm = (d // g) * ds
            Q += ps[i] * float(np.sum(ps * lcm.astype(float) ** (-s)))
        ZQ = z * Q
        # H(n)
        kk = np.arange(1, Vi + 1, dtype=float)
        P = np.cumsum(musV * kk ** (-s))
        Qc = np.cumsum(musV * kk ** (-s) * np.log(kk))
        def M(y):
            y = np.asarray(y, dtype=float)
            out_ = np.zeros_like(y)
            m = y >= 1
            idx = np.floor(y[m]).astype(np.int64) - 1
            out_[m] = P[idx] * np.log(y[m]) - Qc[idx]
            return out_
        n = np.arange(1, Vi + 1, dtype=float)
        H = M(V / n) - M(U / n)
        RHS = z / Delta ** 2 * float(np.sum(H ** 2 * n ** (-s)))
        rank = (eps * X / math.e) ** eps
        boundS = L ** 2 / U + rank * (RHS - 1)
        boundS_exactZQ = L ** 2 / U + rank * (ZQ - 1)
        out.append((eps, ZQ, RHS, boundS_exactZQ, boundS))
    return dict(U=U, V=V, X=X, Y=Y, Delta=Delta, N=N, S=S, rows=out)


if __name__ == "__main__":
    cases = [(50, 2.0, 1.1, 2.5), (100, 2.0, 1.1, 2.5), (200, 2.0, 1.05, 3.0), (60, 2.5, 1.1, 2.0)]
    if len(sys.argv) > 1:
        cases = cases[:int(sys.argv[1])]
    for (U, t, c, L) in cases:
        r = run(U, t, c, L, [0.02, 0.04, 0.06, 0.08, 0.1, 0.13])
        print(f"U={U} V={r['V']:.4g} X={r['X']:.4g} Y={r['Y']:.4g} Delta={r['Delta']:.3f} N={r['N']:.3g}")
        print(f"   brute-force S = {r['S']:.6f}")
        for (eps, ZQ, RHS, bS1, bS) in r["rows"]:
            ok1 = ZQ <= RHS * (1 + 1e-12)
            print(f"   eps={eps:.3f}: ZQ={ZQ:.6f}  (A1) RHS={RHS:.6f}  ratio={RHS/ZQ:.4f} {'OK' if ok1 else 'VIOLATED'}"
                  f" | (A2) with exact ZQ: {bS1:.4f} {'OK' if r['S'] <= bS1 else 'VIOLATED'}"
                  f" | Lemma A bound: {bS:.4f} {'OK' if r['S'] <= bS else 'VIOLATED'}")
        sys.stdout.flush()
