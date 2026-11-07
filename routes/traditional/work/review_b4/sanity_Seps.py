"""
sanity_Seps.py -- independent numerical sanity check (review_b4; NOT a proof, float64).

Computes S_eps(N) = sum_{d,e<=N} mu(d)mu(e)/[d,e]^{1+eps} for EVERY integer N <= NMAX
(S_eps is constant on [N, N+1)), via the increment
   S(N) - S(N-1) = mu(N)^2 N^{-s} + 2 mu(N) N^{-s} sum_{l | N} phi_s(l) A_l(N-1),
   A_l(M) = sum_{e<=M, l|e} mu(e) e^{-s},   phi_s(l) = prod_{p|l} (p^s - 1)  (l squarefree),
which follows from 1/[d,e]^s = (d,e)^s/(de)^s and (d,e)^s = sum_{l|(d,e)} phi_s(l).
Written from scratch (no code shared with audit_rza/).

Cross-checks: exact Fractions (eps=0, N<=300) and Arb double sum (eps>0, N<=200).
Usage: python -I sanity_Seps.py NMAX eps1,eps2,...
"""
import sys, time, json, math
import numpy as np


def mobius_sieve(n):
    mu = np.ones(n + 1, dtype=np.int8)
    mu[0] = 0
    isp = np.ones(n + 1, dtype=bool); isp[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if isp[i]:
            isp[i * i::i] = False
    primes = np.nonzero(isp)[0]
    for p in primes:
        mu[p::p] *= -1
        if p * p <= n:
            mu[p * p::p * p] = 0
    return mu, primes


def phi_s_array(n, primes, s, mu):
    """phi_s(l) = prod_{p|l}(p^s-1) for squarefree l (0 elsewhere)."""
    ph = np.ones(n + 1)
    for p in primes:
        ph[p::p] *= (float(p) ** s - 1.0)
    ph[mu == 0] = 0.0
    return ph


def S_all(nmax, eps, mu, primes):
    s = 1.0 + eps
    idx = np.arange(nmax + 1, dtype=np.float64)
    idx[0] = 1.0
    ns = idx ** (-s)
    x = mu.astype(np.float64) * ns
    x[0] = 0.0
    ph = phi_s_array(nmax, primes, s, mu)
    inc = np.zeros(nmax + 1)
    sqf = np.nonzero(mu)[0]
    for l in sqf.tolist():
        v = x[l::l]
        ex = np.cumsum(v) - v
        inc[l::l] += ph[l] * ex
    dS = (mu.astype(np.float64) ** 2) * ns + 2.0 * mu.astype(np.float64) * ns * inc
    dS[0] = 0.0
    return np.cumsum(dS)


def check_small(mu):
    from fractions import Fraction
    from math import gcd
    # exact eps = 0 double sum for N <= 300
    N = 300
    sq = [k for k in range(1, N + 1) if mu[k] != 0]
    exact = {}
    for M in (1, 2, 10, 42, 100, 300):
        tot = Fraction(0)
        for d in sq:
            if d > M: break
            for e in sq:
                if e > M: break
                tot += Fraction(int(mu[d]) * int(mu[e]) * gcd(d, e), d * e)
        exact[M] = tot
    return exact


def check_arb(mu, eps_s, Ms=(10, 50, 200)):
    from flint import arb, ctx
    from math import gcd
    ctx.prec = 100
    e = arb(eps_s); s = 1 + e
    out = {}
    for M in Ms:
        tot = arb(0)
        sq = [k for k in range(1, M + 1) if mu[k] != 0]
        for d in sq:
            for f in sq:
                L = d * f // gcd(d, f)
                tot += int(mu[d]) * int(mu[f]) * (-s * arb(L).log()).exp()
        out[M] = tot
    return out


def main():
    nmax = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10 ** 6
    epss = [float(t) for t in sys.argv[2].split(",")] if len(sys.argv) > 2 else [0.0, 0.001, 0.01, 0.0227]
    t0 = time.time()
    mu, primes = mobius_sieve(nmax)
    print("sieve done %.1f s" % (time.time() - t0), flush=True)
    ex = check_small(mu)
    res = {}
    for eps in epss:
        t1 = time.time()
        S = S_all(nmax, eps, mu, primes)
        if eps == 0.0:
            for M, v in ex.items():
                assert abs(S[M] - float(v)) < 1e-12, (M, S[M], float(v))
        else:
            for M, v in check_arb(mu, repr(eps)).items():
                assert abs(S[M] - float(v.mid())) < 1e-12, (M, S[M], v)
        rows = []
        lo = 1
        while lo <= nmax:
            hi = min(10 * lo, nmax + 1)
            seg = S[lo:hi]
            k = int(np.argmax(seg))
            rows.append((lo, hi - 1, float(seg.max()), lo + k, float(seg.min()), float(seg[-1])))
            lo = hi
        res[eps] = dict(rows=rows, final=float(S[nmax]), maxall=float(S[1:].max()),
                        max_ge_1000=float(S[1000:].max()) if nmax >= 1000 else None, time=time.time() - t1)
        print("eps=%-8g  time %.1f s   S(NMAX=%d) = %.10f" % (eps, time.time() - t1, nmax, S[nmax]), flush=True)
        for r in rows:
            print("   N in [%d,%d]: max %.8f at %d, min %.8f, at right end %.8f" % r)
        np.save("S_%g_%d.npy" % (eps, nmax), S[::max(1, nmax // 100000)])
    json.dump({repr(k): v for k, v in res.items()}, open("sanity_Seps_%d.json" % nmax, "w"), indent=1)
    print("exact eps=0 values:", {M: float(v) for M, v in ex.items()})
    print("total %.1f s" % (time.time() - t0))


if __name__ == "__main__":
    main()
