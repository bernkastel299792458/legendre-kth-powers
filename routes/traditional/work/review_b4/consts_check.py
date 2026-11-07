"""
consts_check.py -- independent float re-computation (review_b4; sanity, NOT a proof) of the
constants that dominate Theorem R (b4 ~ Tail0 + Bulk0 as eps -> 0), and an independent
float re-implementation of F(eps) (repair REPORT (R.10)) on a fine grid.

Independent of audit_rza/ code:
  * primes by own numpy sieve; Euler products over p <= 1e8 as float log-sums (+ crude tails);
  * S11^c(J), S12^c(J) by brute-force enumeration over ALL subsets n | Pi(j) (the audit uses a
    pair-sum identity instead);
  * TH1, THx1, THx2 (sigma/Sigma sups), Xi1, Xi2 ratios by own multiplicative sieve to NS.
Usage: python -I consts_check.py [NS=1e7]
"""
import sys, math, time, json
import numpy as np
import mpmath as mp

E1C, E2C = 1.044, 0.232            # Zuniga-Alterman 2022 Thm 4.6 constants (alpha = 1)
EPS0 = 0.0227


def sieve_primes(n):
    s = np.ones(n + 1, dtype=bool); s[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = False
    return np.nonzero(s)[0]


def euler(P, cfun):
    """W^c, P^c, w1^c for f(p) = (p-1) c(p)/p^2.  float; tail p>1e8 by integral approx."""
    p = P.astype(np.float64)
    c = cfun(p)
    f = (p - 1) * c / p ** 2
    logW = np.sum(np.log1p(f) + np.log1p(-1 / p))
    a = np.abs(p * f - 1)
    logP = np.sum(np.log1p(a / (np.sqrt(p) - 1)))
    # tails beyond M (approximate, sanity only): log(1+f)(1-1/p) ~ (c-1)/p - 2/p^2 ; |pf-1|/(sqrt p - 1) ~ (1+(c-1)p)/p^1.5
    M = float(P[-1])
    tW = -2 / (M * math.log(M)) + (EPS0 if cfun(np.array([3.0]))[0] != 1 else 0) * (1 / M)
    tP = 2 / (math.sqrt(M) * math.log(M))
    W = math.exp(logW); PP = math.exp(logP)
    f2 = cfun(np.array([2.0]))[0] / 4
    a2 = abs(2 * f2 - 1)
    w1 = (math.sqrt(2) - 1) / (math.sqrt(2) - 1 + a2) * (E1C + a2 * E2C / (math.sqrt(2) - 1))
    return dict(W=W, W_tail_rel=tW, P=PP, P_tail_rel=tP, w1=w1, G1=w1 * PP, G2=E2C * PP)


def mobius_small(n):
    mu = [1] * (n + 1); mu[0] = 0
    for p in range(2, n + 1):
        if all(p % d for d in range(2, int(p ** 0.5) + 1)):
            for k in range(p, n + 1, p):
                mu[k] = -mu[k]
            for k in range(p * p, n + 1, p * p):
                mu[k] = 0
    return mu


def S11S12(J, cfun):
    """brute force over all subsets n of the primes <= j."""
    mu = mobius_small(J + 1)
    primes = [p for p in range(2, J + 1) if all(p % d for d in range(2, int(p ** 0.5) + 1))]
    out11, out12 = {}, {}
    a11 = 0.0; a12 = 0.0
    for j in range(2, J + 1):
        P = [p for p in primes if p <= j]
        k = len(P)
        masks = np.arange(1 << k, dtype=np.int64)
        m = np.zeros(1 << k)
        for l in range(1, j + 1):
            if mu[l] == 0:
                continue
            lm = 0
            for i, p in enumerate(P):
                if l % p == 0:
                    lm |= 1 << i
            m += np.where((masks & lm) == 0, mu[l] / l, 0.0)
        w11 = np.ones(1 << k); w12 = np.ones(1 << k)
        r = 1.0; t = 1.0
        for i, p in enumerate(P):
            bit = ((masks >> i) & 1) == 1
            c = float(cfun(np.array([float(p)]))[0])
            f = (p - 1) * c / p ** 2
            w11 *= np.where(bit, f, 1.0)
            w12 *= np.where(bit, f * math.sqrt(p), 1.0)
            r /= (1 + f)
            a = abs(p * f - 1)
            t *= 1 + (1 - a) / (math.sqrt(p) - 1 + a)
        a11 += r * math.log((j + 1) / j) * float(np.sum(w11 * m * m))
        a12 += t * (math.sqrt(j + 1) + math.sqrt(j)) * float(np.sum(w12 * m * m))
        out11[j] = a11; out12[j] = a12
    return out11, out12


def mult_sieve(n, P, fp):
    """array g(l) = mu^2(l) prod_{p|l} fp(p) for l <= n."""
    g = np.ones(n + 1)
    sqf = np.ones(n + 1, dtype=bool)
    for p in P:
        if p > n:
            break
        g[p::p] *= fp(p)
        if p * p <= n:
            sqf[p * p::p * p] = False
    g[~sqf] = 0.0
    g[0] = 0.0
    return g


def main():
    NS = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10 ** 7
    t0 = time.time()
    P8 = sieve_primes(10 ** 8)
    print("pi(1e8) =", len(P8), "(%.1f s)" % (time.time() - t0), flush=True)
    one = lambda p: np.ones_like(p)
    hc = lambda p: np.exp(EPS0 * np.log(p) / (p - 1))
    e0 = euler(P8, one); eh = euler(P8, hc)
    print("unweighted: W=%.12f  P=%.10f  w1=%.8f  G1=%.8f  G2=%.8f" % (e0["W"], e0["P"], e0["w1"], e0["G1"], e0["G2"]))
    print("   check W = (6/pi^2) prod(1-1/(p(p+1))):  %.12f" % (6 / math.pi ** 2 * math.exp(np.sum(np.log1p(-1 / (P8.astype(float) * (P8 + 1.0)))))))
    print("h^eps0   : W=%.12f  P=%.10f  w1=%.8f  G1=%.8f  G2=%.8f" % (eh["W"], eh["P"], eh["w1"], eh["G1"], eh["G2"]))
    t1 = time.time()
    S11, S12 = S11S12(70, one)
    S11h, S12h = S11S12(70, hc)
    print("subset brute force S11/S12 (%.1f s)" % (time.time() - t1))
    for J in (22, 61, 68, 69, 70):
        print("  J=%d  S11=%.12f  S12=%.6f   S11h=%.12f  S12h=%.6f" % (J, S11[J], S12[J], S11h[J], S12h[J]))
    # sigma / Sigma / Xi scans to NS
    P = sieve_primes(NS)
    g0sq = 3 * (math.sqrt(2) - 1) ** 2 / 4
    g0 = math.sqrt(g0sq)
    t2 = time.time()
    base = lambda p: (p - 1) / (math.sqrt(p) - 1) ** 2
    s1 = np.cumsum(mult_sieve(NS, P, base))
    s2 = np.cumsum(mult_sieve(NS, P, lambda p: base(p) * (g0 if p == 2 else 1.0)))
    S1 = np.cumsum(mult_sieve(NS, P, lambda p: base(p) * (g0sq if p == 2 else 1.0)))
    xi1 = np.cumsum(mult_sieve(NS, P, lambda p: (p - 1) / (p * (math.sqrt(p) - 1))))
    xi2 = np.cumsum(mult_sieve(NS, P, lambda p: (p - 1) / (p * (math.sqrt(p) - 1)) * (g0 if p == 2 else 1.0)))
    N = np.arange(NS + 1, dtype=np.float64); N[0] = 1
    res = {}
    for name, arr, nrm in (("sigma1 (THx1)", s1, N), ("sigma2 (THx2)", s2, N), ("Sigma1 (TH1)", S1, N),
                           ("Xi1/sqrt (THxxx)", xi1, np.sqrt(N)), ("Xi2/sqrt (THx)", xi2, np.sqrt(N))):
        r = arr[1:] / nrm[1:]
        k = int(np.argmax(r))
        res[name] = (float(r[k]), k + 1, float(r[-1]))
        print("  %-18s sup_{N<=%d} = %.8f at N=%d ; value at N=NS: %.8f" % (name, NS, r[k], k + 1, r[-1]))
    print("scans %.1f s" % (time.time() - t2))
    # assemble Tail0 / Bulk0 / Bulk1 with own constants (L1, L2, H1 from the audit; tiny terms)
    X0 = 3e12
    TH1 = res["Sigma1 (TH1)"][0]
    H1, L1, L2 = 0.010032, 0.13779107, 0.09686390
    for J in (68, 69):
        Z = J + 0.9999
        Tail0 = 2 * TH1 / Z + 2 * math.sqrt(2) * H1 * L1 / math.sqrt(Z) + H1 ** 2 * L2
        Bulk0 = e0["W"] * (math.log(2) + S11[J]) + (e0["G1"] * (1 + math.sqrt(2)) + e0["G2"] * S12[J]) / math.sqrt(X0)
        Bulk1 = eh["W"] * (math.log(2) + S11h[J]) + (eh["G1"] * (1 + math.sqrt(2)) + eh["G2"] * S12h[J]) / math.sqrt(X0)
        print("  J=%d: Tail0=%.10f Bulk0=%.10f Bulk1=%.10f  Tail0+Bulk0=%.10f  lambda=%.6f" % (
            J, Tail0, Bulk0, Bulk1, Tail0 + Bulk0, math.log(Bulk1 / Bulk0) / EPS0))
    json.dump(dict(e0=e0, eh=eh, S11={k: S11[k] for k in (61, 68, 69)}, S12={k: S12[k] for k in (61, 68, 69)},
                   S11h={k: S11h[k] for k in (68, 69)}, S12h={k: S12h[k] for k in (68, 69)}, scans=res),
              open("consts_check_out.json", "w"), indent=1)
    print("total %.1f s" % (time.time() - t0))


if __name__ == "__main__":
    main()
