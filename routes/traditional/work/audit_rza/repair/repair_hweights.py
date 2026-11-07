"""
repair_hweights.py -- the h-weighted ("Bulk1") ingredients of the repaired b4 lemma.

Weight: c(p) = h(p)^{eps0} = p^{eps0/(p-1)} (multiplicative, squarefree support).  It dominates
c_eps(p) = (p^{1+eps}-1)/(p^eps (p-1)) for every 0 < eps <= eps0 in the Hoelder form
c_eps(l) <= h(l)^eps = (h(l)^{eps0})^{eps/eps0}  (REPORT.md, Lemma R1).

Computes, in Arb:
  W^h   = prod_p (1+f(p))(1-1/p),          f(p) = (p-1)c(p)/p^2       (upper bound)
  P^h   = prod_p (1 + |p f(p) - 1|/(sqrt p - 1))                         (upper bound)
  G1^h  = w_1^h P^h  (q odd),   G2^h = E_1^{(2)} P^h  (q even)           [Thm 4.2(A), alpha=1]
  S11^h(J) = sum_{1<j<=J} r^h_{Pi(j)} log((j+1)/j) sum_{n|Pi(j)} mu^2(n)phi(n)c(n)/n^2   m_n(j)^2
  S12^h(J) = sum_{1<j<=J} t^h_{Pi(j)} (sqrt(j+1)+sqrt j) sum_{n|Pi(j)} mu^2(n)phi(n)c(n)/n^{3/2} m_n(j)^2
with r^h_q = prod_{p|q} 1/(1+f(p)),  t^h_q = prod_{p|q} (1 + (1-|pf-1|)/(sqrt p - 1 + |pf-1|)).

Usage: python -I repair_hweights.py EPS0 [JMAX]     (EPS0 as a decimal string, e.g. 0.0227)
Output: out/hweights_<EPS0>.json
"""
import os, sys, json, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import numpy as np
from multiprocessing import Pool

MAXP = 10 ** 8


def cfac(P, e0):
    from flint import arb
    return (e0 * P.log() / (P - 1)).exp()


def worker(args):
    ps, e0s, prec = args
    from flint import arb, ctx
    ctx.prec = prec
    e0 = arb(e0s)
    W = arb(1); Pp = arb(1)
    for p in ps.tolist():
        P = arb(p)
        c = cfac(P, e0)
        f = (P - 1) * c / P ** 2
        W *= (1 + f) * (1 - 1 / P)
        Pp *= 1 + abs(P * f - 1) / (P.sqrt() - 1)
    return [W.mid().str(40, radius=False), W.rad().str(5, radius=False),
            Pp.mid().str(40, radius=False), Pp.rad().str(5, radius=False)]


def main():
    e0s = sys.argv[1] if len(sys.argv) > 1 else "0.0227"
    JMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 90
    t0 = time.time()
    from flint import arb, ctx
    import rza_common as rc
    from rza_euler import primes_upto
    from rza_thm11 import inner_full, primes_upto as small_primes
    ctx.prec = 128
    e0 = arb(e0s)
    allp = primes_upto(MAXP)
    assert len(allp) == 5761455
    with Pool(16) as pool:
        parts = pool.map(worker, [(ch, e0s, 128) for ch in np.array_split(allp, 64)])
    W = arb(1); Pp = arb(1)
    for a in parts:
        W *= arb(a[0], a[1]) + arb(0, "1e-38")
        Pp *= arb(a[2], a[3]) + arb(0, "1e-38")
    Mv = arb(MAXP)
    # tails (REPORT.md Lemma R4): factor-1 <= 1.000001 eps0 log p / p^2 ; |pf-1|/(sqrt p-1) <= (1+1.000001 eps0 log p)/(p^{3/2}(1-M^-1/2))
    k = arb("1.000001")
    W_up = W * (k * e0 * rc.C_kappa(2) / (1 - 1 / Mv)).exp()
    P_up = Pp * ((rc.B_kappa(arb(3) / 2) + k * e0 * rc.C_kappa(arb(3) / 2)) / (1 - rc.rpow(Mv, -arb(1) / 2))).exp()
    E1, E2 = arb("1.044"), arb("0.232")
    f2 = cfac(arb(2), e0) / 4
    w1 = (rc.SQ2 - 1) / (rc.SQ2 - 1 + abs(2 * f2 - 1)) * (E1 + abs(2 * f2 - 1) * E2 / (rc.SQ2 - 1))
    G1h, G2h = w1 * P_up, E2 * P_up
    # finite sums
    fw11 = lambda p: arb(p - 1) * cfac(arb(p), e0) / arb(p) ** 2
    fw12 = lambda p: arb(p - 1) * cfac(arb(p), e0) / arb(p) ** arb(1.5)
    def rq(j):
        v = arb(1)
        for p in small_primes(j):
            v /= 1 + fw11(p)
        return v
    def tq(j):
        v = arb(1)
        for p in small_primes(j):
            a = abs(p * fw11(p) - 1)
            v *= 1 + (1 - a) / (arb(p).sqrt() - 1 + a)
        return v
    S11, S12 = {}, {}
    a11 = arb(0); a12 = arb(0)
    for j in range(2, JMAX + 1):
        a11 += rq(j) * (arb(j + 1) / j).log() * inner_full(j, fw11)
        a12 += tq(j) * (arb(j + 1).sqrt() + arb(j).sqrt()) * inner_full(j, fw12)
        S11[j] = [a11.mid().str(25, radius=False), a11.rad().str(3, radius=False)]
        S12[j] = [a12.mid().str(25, radius=False), a12.rad().str(3, radius=False)]
    out = dict(eps0=e0s, W_M=W.str(20), W_up=[W_up.upper().str(25, radius=False)],
               P_M=Pp.str(20), P_up=[P_up.upper().str(25, radius=False)],
               G1h=[G1h.upper().str(25, radius=False)], G2h=[G2h.upper().str(25, radius=False)],
               S11=S11, S12=S12)
    os.makedirs(os.path.join(HERE, "out"), exist_ok=True)
    json.dump(out, open(os.path.join(HERE, "out", "hweights_%s.json" % e0s), "w"), indent=0)
    print("eps0=%s  W^h(p<=1e8)=%s  W^h_up=%s  P^h_up=%s  G1^h=%s  G2^h=%s" % (
        e0s, W.str(12), W_up.upper().str(12, radius=False), P_up.upper().str(12, radius=False),
        G1h.upper().str(10, radius=False), G2h.upper().str(10, radius=False)))
    for J in (22, 61, 68, 80, JMAX):
        if J in S11:
            print("  J=%d  S11^h=%s  S12^h=%s" % (J, arb(*S11[J]).str(12), arb(*S12[J]).str(10)))
    print("time %.1f s" % (time.time() - t0))


if __name__ == "__main__":
    main()
