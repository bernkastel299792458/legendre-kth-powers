"""
repair_hf_inputs.py -- constants of the Helfgott-free variant (REPORT.md, Lemma R2'):

  inputs:  (own)   |m(t)| <= sqrt(2/t), |m_2(t)| <= sqrt(3/t) for t <= N        (repair_mcert.py)
           (refereed) |m(x)| <= 0.0144/log x for x >= 96955   (Ramare, Math. Comp. 84 (2015), Thm 1.2)
  outputs: H2' with |m_2(t)| <= H2'/log t for t >= N, from m_2(t) = sum_{k>=0} 2^{-k} m(t/2^k);
           T_N = sup_{y>=N} (log y / y) int_N^y dt/log t   (rigorous cell cover + analytic tail).
Run: python -I repair_hf_inputs.py [log10N=10]
"""
import os, sys, json
from flint import arb, ctx
ctx.prec = 128
HERE = os.path.dirname(os.path.abspath(__file__))


def H2prime(N):
    N = arb(N)
    LN = N.log()
    x0 = arb(96955)
    l0 = x0.log()
    L2 = arb(2).log()
    S = arb(0)
    K = 400
    for k in range(K + 1):
        Lk = LN.max(l0 + k * L2)
        S += arb(2) ** (-k) * Lk / (Lk - k * L2)
    # tail k > K: Lk = l0 + k log 2, term = 2^-k (1 + k log2/l0) <= 2^-k (1 + k)
    S += arb(2) ** (-K) * (K + 3)          # sum_{k>K} 2^-k (1+k) = 2^-K (K+2) <= 2^-K (K+3)
    second = (2 * x0).sqrt() * LN / (N * (1 - 1 / arb(2).sqrt()))
    return arb("0.0144") * S + second, S, second


def T_N(N, du=arb("1e-4")):
    N = arb(N)
    uN = N.log()
    liN = N.li()
    u = uN
    best = arb(0)
    ucap = 3 * uN
    n = 0
    while bool(u < ucap):
        u2 = u + du
        g = u * (-u).exp() * (u2.exp().li() - liN)
        best = best.max(g)
        u = u2
        n += 1
    # analytic tail u >= 3 log N:  g <= 1 + 1/u + 2u e^{-u/2}/log^3 N + 16/u^2  (decreasing in u there)
    tail = 1 + 1 / ucap + 2 * ucap * (-ucap / 2).exp() / uN ** 3 + 16 / ucap ** 2
    return best.max(tail), best, tail, n


if __name__ == "__main__":
    lg = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    N = arb(10) ** lg
    h2, S, sec = H2prime(N)
    T, grid, tail, n = T_N(N)
    print("N = 1e%d" % lg)
    print("  H2' = 0.0144*%s + %s = %s   (|m_2(t)| <= H2'/log t, t >= N)" % (S.str(10), sec.str(3), h2.upper().str(10, radius=False)))
    print("  T_N = %s  (grid max %s over %d cells, analytic tail bound %s)" % (T.upper().str(10, radius=False), grid.str(8), n, tail.str(6)))
    os.makedirs(os.path.join(HERE, "out"), exist_ok=True)
    json.dump(dict(log10N=lg, H2p=h2.upper().str(20, radius=False), T_N=T.upper().str(20, radius=False)),
              open(os.path.join(HERE, "out", "hf_inputs_1e%d.json" % lg), "w"), indent=1)
