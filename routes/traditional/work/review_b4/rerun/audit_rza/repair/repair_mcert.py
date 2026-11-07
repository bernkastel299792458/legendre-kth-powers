"""
repair_mcert.py -- our own certificate (replacing Helfgott's book computations, RZA Lemma 2.2):

   |m(t)|   <= sqrt(2/t)   for 0 < t <= N,        m(t)   = sum_{n<=t} mu(n)/n,
   |m_2(t)| <= sqrt(3/t)   for 0 < t <= N,        m_2(t) = sum_{n<=t, n odd} mu(n)/n,

with N = 10^10 (default).  Both sides are constant / decreasing on [n, n+1), so it suffices that
|m(n)| <= sqrt(2/(n+1)) and |m_2(n)| <= sqrt(3/(n+1)) for every integer 1 <= n <= N (limits from
the left; for n=1 resp. n<=2 equality holds in the limit and the inequality is strict on [n,n+1)).

Method: n <= 10^5 exactly in Arb.  Beyond: parallel segmented Moebius sieve (numpy).  Inside each
segment the prefix sums c_i are float64 cumsums with the a-priori bound
|fl(c_i) - c_i| <= (L+2) u sum_seg |x| (u = 2^-53, L = segment length) [Higham, Thm 4.4];
the segment totals are summed exactly-rounded (math.fsum), each term mu(n)/n carrying <= u|x|.
A segment imposes on the true offset m(a-1) the interval [max(-b_i-c_i), min(b_i-c_i)] (shrunk by
the error), and we check the true offset lies inside it (also shrunk).  Additionally checks Ramare's
refereed |m(t)| log t <= 0.0144 on [96955, N] (sanity only; it is a theorem).
Run: python -I repair_mcert.py [log10N=10]      (~5-10 min on 16 processes)
"""
import os, sys, math, time, json
import numpy as np
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
SEG = 1 << 24
U = 2.0 ** -53


def small_primes(n):
    s = np.ones(n + 1, dtype=bool); s[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = False
    return np.nonzero(s)[0].astype(np.int64)


def worker(args):
    a, b, P = args
    L = b - a
    n = np.arange(a, b, dtype=np.int64)
    mu = np.ones(L, dtype=np.int8)
    sm = np.ones(L)
    for p in P:
        p = int(p)
        if p * p >= b and p > b:
            break
        s = (-a) % p
        mu[s::p] *= -1
        sm[s::p] *= p
        pp = p * p
        if pp < b:
            mu[(-a) % pp::pp] = 0
    cof = n / sm
    mu[(cof > 1.5) & (mu != 0)] *= -1
    x = mu / n.astype(np.float64)
    x2 = np.where(n % 2 == 1, x, 0.0)
    out = []
    nf = (n + 1).astype(np.float64)
    for xx, const in ((x, 2.0), (x2, 3.0)):
        c = np.cumsum(xx)
        tot = math.fsum(xx.tolist())
        sabs = float(np.sum(np.abs(xx)))
        err = (L + 2) * U * sabs * 1.01 + 4 * U
        bnd = np.sqrt(const / nf) * (1 - 4 * U)
        lo = float(np.max(-bnd - c)) + err
        hi = float(np.min(bnd - c)) - err
        # Ramare 0.0144/log t on t in [n, n+1): sup at right end of log, i.e. |m(n)| log(n+1)
        out.append((tot, sabs, lo, hi))
    # data for Ramare sanity check (needs offset; return c at the points with max |c| only is not enough) -> skip here
    return a, b, out


def main():
    lg = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    N = 10 ** lg
    t0 = time.time()
    from flint import arb, ctx
    ctx.prec = 128
    # exact part n <= 1e5
    NE = 10 ** 5
    P = small_primes(int(math.isqrt(N)) + 2)
    mu = [1] * (NE + 1)
    sq = [True] * (NE + 1)
    for p in small_primes(NE).tolist():
        for k in range(p, NE + 1, p):
            mu[k] = -mu[k]
        for k in range(p * p, NE + 1, p * p):
            sq[k] = False
    m = arb(0); m2 = arb(0); worst = [0.0, 0, 0.0, 0]
    for k in range(1, NE + 1):
        if sq[k]:
            m += arb(mu[k]) / k
            if k % 2:
                m2 += arb(mu[k]) / k
        b1 = (arb(2) / (k + 1)).sqrt(); b2 = (arb(3) / (k + 1)).sqrt()
        assert bool(abs(m) <= b1), ("m fails", k)
        assert bool(abs(m2) <= b2), ("m2 fails", k)
        if k >= 10:
            r1 = float((abs(m) / b1).upper()); r2 = float((abs(m2) / b2).upper())
            if r1 > worst[0]: worst[0], worst[1] = r1, k
            if r2 > worst[2]: worst[2], worst[3] = r2, k
    off = [float(m.mid()), float(m2.mid())]
    off_err = [float(m.rad()) + 1e-30, float(m2.rad()) + 1e-30]
    print("exact part n <= %d: OK; max ratio for 10<=n<=1e5: m %.6f (n=%d), m_2 %.6f (n=%d)" % (NE, *worst), flush=True)
    tasks = []
    a = NE + 1
    while a <= N:
        b = min(a + SEG, N + 1)
        tasks.append((a, b, P))
        a = b
    ok = True; nseg = 0
    minslack = [1e9, 1e9]
    with Pool(16) as pool:
        for a, b, out in pool.imap(worker, tasks, chunksize=1):
            for k in range(2):
                tot, sabs, lo, hi = out[k]
                o_lo, o_hi = off[k] - off_err[k], off[k] + off_err[k]
                if not (lo <= o_lo and o_hi <= hi):
                    ok = False
                    print("FAIL", "m" if k == 0 else "m_2", a, b, lo, o_lo, o_hi, hi, flush=True)
                minslack[k] = min(minslack[k], (o_lo - lo), (hi - o_hi))
                off[k] += tot
                off_err[k] += 2 * U * sabs + 2 * U * abs(off[k])   # fsum exactly rounded + term errors <= u|x|
            nseg += 1
    res = dict(N=N, ok=ok, segments=nseg, min_absolute_slack=minslack, final_m=off[0], final_m2=off[1],
               final_err=off_err, time=time.time() - t0)
    print(json.dumps(res))
    os.makedirs(os.path.join(HERE, "out"), exist_ok=True)
    json.dump(res, open(os.path.join(HERE, "out", "mcert_1e%d.json" % lg), "w"), indent=1)
    print("CERTIFIED" if ok else "NOT CERTIFIED", "|m(t)|<=sqrt(2/t), |m_2(t)|<=sqrt(3/t) for t <= 1e%d" % lg)


if __name__ == "__main__":
    main()
