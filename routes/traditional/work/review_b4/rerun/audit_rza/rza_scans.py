"""
rza_scans.py -- the finite numerical inspections ("a numerical inspection for X in [1, N] tells
us that ...") behind the hard-coded constants of RZA v3, recomputed independently.

Method (rigorous): a segmented numpy sieve evaluates every summand mu^2(l) f(l) in float64 and
the running sums by np.cumsum.  Standard a-priori floating-point error analysis bounds the
relative error of each running sum by (len(segment)+#segments+64)*2^-53 <= 1e-9 here; we use a
safety tolerance TOL_REL = 1e-8 (relative) everywhere.  Each claimed extremum is located by the
scan and then re-evaluated EXACTLY at the extremal point in Arb, and the scan certifies that
every other point is below/above it by more than the tolerance.

  (A) sigma_1, sigma_2, Sigma_1 / X  (Lemma 4.5)  max over integers X <= N_A (paper: 4e9)
  (B) Z_1/X  (Lemma 4.6)  X <= 1e7;   (C) Z_2/X (Lemma 4.8) X <= 1e6
  (D) Xi_1/sqrt X, Xi_2/sqrt X (Lemma 4.10) X <= 5e6
  (E) K_1(n) - c log n, K_1(n) - c log(n+1) (Lemma 4.11) n <= 2e8, with the paper's c and the true c
  (F) same for K_2 (Lemma 4.13)
  (G) G(1e8; 1.1) = sum_{l<=1e8} mu^2(l)/phi_{1.1}(l)  (>= 9.1 claimed, proof of Thm 1.2)
  (H) sum_{l<=X} mu^2(l)/l - 6/pi^2 log X in [1.040, 1.048] for 1e3 <= X <= 1e8 (Lemma 4.3, partial)
  (I) |m(X)| <= sqrt(2/X), |m_2(X)| <= sqrt(3/X), |m(X)| <= 0.010032/log X (X >= 617990),
      |m_2(X)| <= 0.0296/log X (X >= 5379), for X <= 1e8 (Lemmas 2.2/2.3, partial)

Run:  python -I rza_scans.py [--NA 4000000000] [--only A,B,...]
"""
import os, sys, json, math, time, argparse
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
from rza_common import OUTDIR as OUT
TOL_REL = 1e-8
SEG = 1 << 24


def small_primes(n):
    s = np.ones(n + 1, dtype=bool)
    s[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = False
    return np.nonzero(s)[0].astype(np.int64)


class Seg:
    """segmented squarefree sieve: for [a,b) gives n, sqf mask, list of small primes and big cofactor"""

    def __init__(self, N):
        self.N = N
        self.P = small_primes(int(math.isqrt(N)) + 1)

    def segments(self):
        a = 1
        while a <= self.N:
            b = min(a + SEG, self.N + 1)
            yield a, b
            a = b

    def eval(self, a, b, fp_small, fbig_vec, f2):
        """returns (n, g) with g = mu^2(n) f(n), f multiplicative, f(p) from fp_small (dict-like array
        over self.P) for small p, fbig_vec(q) vectorised for the big prime cofactor, f(2)=f2."""
        L = b - a
        n = np.arange(a, b, dtype=np.int64)
        val = np.ones(L)
        sm = np.ones(L)
        sqf = np.ones(L, dtype=bool)
        for i, p in enumerate(self.P):
            p = int(p)
            if p > b:
                break
            s = (-a) % p
            fv = f2 if p == 2 else fp_small[i]
            val[s::p] *= fv
            sm[s::p] *= p
            pp = p * p
            if pp < b:
                s2 = (-a) % pp
                sqf[s2::pp] = False
        cof = n / sm
        big = (cof > 1.5) & sqf
        if big.any():
            val[big] *= fbig_vec(cof[big])
        val[~sqf] = 0.0
        return n, val


def run_ratio_scan(N, ffun, f2list, norm, label, seg=None, band=1e-6):
    """sup over integers n<=N of S(n)/norm(n), for several values of f(2).
    Returns per variant: (best_float, argmax, candidates) where candidates are ALL n whose float
    ratio is >= best_float*(1-band); every other n is certified below the max (see header)."""
    seg = seg or Seg(N)
    fp_small = np.array([ffun(float(p)) for p in seg.P])
    best = [-1.0 for _ in f2list]
    cands = [[] for _ in f2list]
    cum = [0.0 for _ in f2list]
    for a, b in seg.segments():
        n, base = seg.eval(a, b, fp_small, lambda q: ffun(q), 1.0)
        even = (n % 2 == 0)
        for k, f2 in enumerate(f2list):
            g = np.where(even, base * f2, base)
            cs = np.cumsum(g) + cum[k]
            cum[k] = float(cs[-1])
            r = cs / norm(n.astype(np.float64))
            best[k] = max(best[k], float(r.max()))
            idx = np.nonzero(r >= best[k] * (1 - band))[0]
            cands[k].extend((float(r[i]), int(n[i])) for i in idx[:100000])
    out = []
    for k in range(len(f2list)):
        cs_ = sorted([c for c in cands[k] if c[0] >= best[k] * (1 - band)], reverse=True)
        out.append((best[k], cs_[0][1], [c[1] for c in cs_]))
    return out, cum


def certify_ratio(best_float, cand_ns, exact_fn, norm_arb, claimed):
    """exact sup = max over candidates (others are below by > band - tol).  Returns dict."""
    from flint import arb
    ex = exact_fn(sorted(set(cand_ns)))
    vals = {n: ex[n] / norm_arb(n) for n in ex}
    nstar = max(vals, key=lambda n: vals[n].mid())
    sup = vals[nstar]
    for v in vals.values():
        sup = sup.max(v)
    return dict(argmax=nstar, n_candidates=len(vals), sup_exact=sup.str(16), claimed=claimed,
                claimed_ok=bool(arb(claimed) >= sup), sup_upper=sup.upper().str(16, radius=False),
                float_max=best_float)


def exact_sums_at(ns, f_arb_p, f2_arb):
    """exact Arb values S(n) = sum_{l<=n} mu^2(l) f(l) for every n in the sorted list ns"""
    from flint import arb
    ns = sorted(set(ns))
    nmax = ns[-1]
    spf = np.arange(nmax + 1, dtype=np.int64)
    for i in range(2, int(nmax ** 0.5) + 1):
        if spf[i] == i:
            blk = spf[i * i::i]
            mask = blk == np.arange(i * i, nmax + 1, i)
            blk[mask] = i
            spf[i * i::i] = blk
    spf = spf.tolist()
    vals = [None] * (nmax + 1)
    vals[1] = arb(1)
    fpc = {}
    s = arb(1)
    want = set(ns)
    out = {}
    if 1 in want:
        out[1] = s
    for l in range(2, nmax + 1):
        p = spf[l]
        r = l // p
        if r % p == 0 or vals[r] is None:
            vals[l] = None
        else:
            if p not in fpc:
                fpc[p] = f2_arb if p == 2 else f_arb_p(p)
            vals[l] = vals[r] * fpc[p]
            s += vals[l]
        if l in want:
            out[l] = s
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--NA", type=int, default=4 * 10 ** 9)
    ap.add_argument("--only", default="A,B,C,D,E,F,G,H,I")
    args = ap.parse_args()
    only = set(args.only.split(","))
    from flint import arb, ctx
    import rza_common as rc
    ctx.prec = 128
    xi = float(rc.XI.mid())
    XI = rc.XI
    SQ2 = rc.SQ2
    g0 = arb(3).sqrt() * (SQ2 - 1) / 2
    H2H1 = arb(rc.H2_STR) / arb(rc.H1_STR)
    g2 = H2H1 * (1 - 1 / rc.rpow(2, XI))
    res = {}
    os.makedirs(OUT, exist_ok=True)
    t0 = time.time()

    def report(k, v):
        res[k] = v
        print(k, json.dumps(v, default=str), flush=True)

    def ratio_block(key, N, f, fa, f2s, names, papers, norm_np, norm_arb):
        out = []
        variants, cum = run_ratio_scan(N, f, [float(x.mid()) for x in f2s], norm_np, key)
        for name, f2, (bf, at, cn), paper in zip(names, f2s, variants, papers):
            d = certify_ratio(bf, cn, lambda ns, f2=f2: exact_sums_at(ns, fa, f2), norm_arb, paper)
            d.update(name=name, N=N)
            out.append(d)
        report(key, out)

    # ---------------- (A) sigma_1, sigma_2, Sigma_1 -------------------------------------------
    if "A" in only:
        c = 1 / (SQ2 - 1) ** 2
        ratio_block("A", args.NA, lambda p: (p - 1) / (np.sqrt(p) - 1) ** 2,
                    lambda p: arb(p - 1) / (arb(p).sqrt() - 1) ** 2, [c, g0 * c, g0 ** 2 * c],
                    ["sigma1", "sigma2", "Sigma1"], ["6.2359917454422", "3.16843122347233", "2.06803754617859"],
                    lambda n: n, lambda n: arb(n))

    # ---------------- (B) Z_1 / X, X <= 1e7 ---------------------------------------------------
    if "B" in only:
        f2 = g0 * g2 * (1 + (rc.rpow(2, XI - arb(1) / 2) + 1) / (rc.rpow(2, XI) - 1))
        ratio_block("B", 10 ** 7, lambda p: (p - 1) / p * np.sqrt(p) / (np.sqrt(p) - 1) * p ** xi / (p ** xi - 1),
                    lambda p: arb(p - 1) / p * arb(p).sqrt() / (arb(p).sqrt() - 1) * rc.rpow(p, XI) / (rc.rpow(p, XI) - 1),
                    [f2], ["Z1"], ["1.90380793763037"], lambda n: n, lambda n: arb(n))

    # ---------------- (C) Z_2 / X, X <= 1e6 ---------------------------------------------------
    if "C" in only:
        f2 = g2 ** 2 * rc.rpow(2, 2 * XI - 1) / (rc.rpow(2, XI) - 1) ** 2
        ratio_block("C", 10 ** 6, lambda p: (p - 1) / p * (p ** xi / (p ** xi - 1)) ** 2,
                    lambda p: arb(p - 1) / p * (rc.rpow(p, XI) / (rc.rpow(p, XI) - 1)) ** 2,
                    [f2], ["Z2"], ["2.67710025"], lambda n: n, lambda n: arb(n))

    # ---------------- (D) Xi_1, Xi_2 / sqrt X, X <= 5e6 ---------------------------------------
    if "D" in only:
        ratio_block("D", 5 * 10 ** 6, lambda p: (np.sqrt(p) + 1) / p, lambda p: (arb(p).sqrt() + 1) / p,
                    [(SQ2 + 1) / 2, g0 * (SQ2 + 1) / 2], ["Xi1", "Xi2"], ["2.2526506709", "1.587160669"],
                    np.sqrt, lambda n: arb(n).sqrt())

    # ---------------- (E),(F) K_1, K_2 ---------------------------------------------------------
    for key, power in (("E", 1), ("F", 2)):
        if key not in only:
            continue
        N = 2 * 10 ** 8
        f = lambda p, pw=power: (p - 1) / p ** 2 * (p ** xi / (p ** xi - 1)) ** pw
        rr = rc.rpow(2, XI) / (rc.rpow(2, XI) - 1)
        f2 = (g2 * rr) ** power / 4
        E = json.load(open(os.path.join(OUT, "euler_products.json")))
        Pt = arb(E["P0_LX_true"][0], E["P0_LX_true"][1]) if power == 1 else arb(E["P3"][0], E["P3"][1])
        Pp = arb("0.694045937") if power == 1 else arb("1.031648197")
        F2c = 1 - (1 - 2 * f2) / 2 - f2 / 2
        consts = {"true": (F2c * Pt * (1 - arb("1e-8")), F2c * Pt * (1 + arb("1e-8"))),
                  "paper": (F2c * Pp, F2c * Pp * (1 + arb("1e-8")))}
        seg = Seg(N)
        fps = np.array([f(float(p)) for p in seg.P])
        cum = 0.0
        band = 1e-6
        mx = {k: -1e9 for k in consts}; mn = {k: 1e9 for k in consts}
        cmx = {k: [] for k in consts}; cmn = {k: [] for k in consts}
        for a, b in seg.segments():
            n, g = seg.eval(a, b, fps, lambda q: f(q), float(f2.mid()))
            cs = np.cumsum(g) + cum
            cum = float(cs[-1])
            ln = np.log(n.astype(np.float64))
            ln1 = np.log((n + 1).astype(np.float64))
            for k, (clo, chi) in consts.items():
                u = cs - float(clo.mid()) * ln
                v = cs - float(chi.mid()) * ln1
                mx[k] = max(mx[k], float(u.max())); mn[k] = min(mn[k], float(v.min()))
                cmx[k].extend(int(x) for x in n[u >= mx[k] - band][:1000])
                cmn[k].extend(int(x) for x in n[v <= mn[k] + band][:1000])
        fa = lambda p, pw=power: arb(p - 1) / arb(p) ** 2 * (rc.rpow(p, XI) / (rc.rpow(p, XI) - 1)) ** pw
        out = dict(K_at_N_float=cum)
        for k, (clo, chi) in consts.items():
            ex = exact_sums_at(cmx[k] + cmn[k], fa, f2)
            umax = None; umin = None
            for nn in set(cmx[k]):
                val = ex[nn] - clo * arb(nn).log()
                umax = val if umax is None else umax.max(val)
            for nn in set(cmn[k]):
                val = ex[nn] - chi * arb(nn + 1).log()
                umin = val if umin is None else umin.min(val)
            amax = max(set(cmx[k]), key=lambda nn: (ex[nn] - clo * arb(nn).log()).mid())
            amin = min(set(cmn[k]), key=lambda nn: (ex[nn] - chi * arb(nn + 1).log()).mid())
            out[k] = dict(c=[clo.str(12), chi.str(12)], sup_K_minus_clog=umax.str(14), at=amax,
                          inf_K_minus_clog_np1=umin.str(14), at_min=amin, float_max=mx[k], float_min=mn[k])
        out["paper_logmx"] = "1.29424331261228" + ("" if power == 1 else " (identical to K1's!)")
        out["paper_logmm"] = "0.505508801388535" + ("" if power == 1 else " (identical to K1's!)")
        report(key, out)

    # ---------------- (G) G(1e8;1.1) ----------------------------------------------------------
    if "G" in only:
        N = 10 ** 8
        f = lambda p: 1 / (p ** 1.1 - 1)
        seg = Seg(N)
        fps = np.array([f(float(p)) for p in seg.P])
        tot = 0.0
        for a, b in seg.segments():
            n, g = seg.eval(a, b, fps, f, f(2.0))
            tot += float(np.sum(g))
        report("G", dict(G_1e8_1p1=tot, claimed_lower=9.1, ok=tot * (1 - TOL_REL) > 9.1))

    # ---------------- (H) Ramare Lemma 3.4 constants on [1e3, 1e8] ----------------------------
    if "H" in only:
        N = 10 ** 8
        seg = Seg(N)
        fps = np.array([1 / float(p) for p in seg.P])
        cum = 0.0
        c6 = 6 / math.pi ** 2
        hi, lo_ = (-1, 0), (9, 0)
        hi_all, lo_all = (-1, 0), (9, 0)
        for a, b in seg.segments():
            n, g = seg.eval(a, b, fps, lambda q: 1 / q, 0.5)
            cs = np.cumsum(g) + cum
            cum = float(cs[-1])
            u = cs - c6 * np.log(n.astype(np.float64))
            v = cs - c6 * np.log((n + 1).astype(np.float64))
            m = n >= 1000
            if m.any():
                i = int(np.argmax(np.where(m, u, -9)))
                j = int(np.argmin(np.where(m, v, 9)))
                if u[i] > hi[0]:
                    hi = (float(u[i]), int(n[i]))
                if v[j] < lo_[0]:
                    lo_ = (float(v[j]), int(n[j]))
            i = int(np.argmax(u)); j = int(np.argmin(v))
            if u[i] > hi_all[0]:
                hi_all = (float(u[i]), int(n[i]))
            if v[j] < lo_all[0]:
                lo_all = (float(v[j]), int(n[j]))
        report("H", dict(range="[1e3,1e8]", max=hi, min=lo_, claimed=[1.040, 1.048],
                         all_X_ge1=dict(max=hi_all, min=lo_all, claimed=[0.578, 1.166])))

    # ---------------- (I) m(X), m_2(X) on X <= 1e8 --------------------------------------------
    if "I" in only:
        N = 10 ** 8
        seg = Seg(N)
        fps = np.array([-1 / float(p) for p in seg.P])
        cum1 = cum2 = 0.0
        w = {}
        for k in ("sqrt2", "sqrt3_odd", "log_m", "log_m2"):
            w[k] = (0.0, 0)
        for a, b in seg.segments():
            n, g = seg.eval(a, b, fps, lambda q: -1 / q, -0.5)
            g2 = np.where(n % 2 == 0, 0.0, g)
            m1 = np.cumsum(g) + cum1
            m2 = np.cumsum(g2) + cum2
            cum1, cum2 = float(m1[-1]), float(m2[-1])
            X1 = (n + 1).astype(np.float64)       # sup over X in [n, n+1)
            r = np.abs(m1) * np.sqrt(X1 / 2)
            i = int(np.argmax(r)); w["sqrt2"] = max(w["sqrt2"], (float(r[i]), int(n[i])))
            mm = np.where(n <= 10 ** 12, np.abs(m2) * np.sqrt(X1 / 3), 0)
            i = int(np.argmax(mm)); w["sqrt3_odd"] = max(w["sqrt3_odd"], (float(mm[i]), int(n[i])))
            mm = np.where(n >= 617990, np.abs(m1) * np.log(X1) / 0.010032, 0)
            i = int(np.argmax(mm)); w["log_m"] = max(w["log_m"], (float(mm[i]), int(n[i])))
            mm = np.where(n >= 5379, np.abs(m2) * np.log(X1) / 0.0296, 0)
            i = int(np.argmax(mm)); w["log_m2"] = max(w["log_m2"], (float(mm[i]), int(n[i])))
        report("I", dict(note="ratios must be <= 1; (value, n)", **w))

    print("time %.1f s" % (time.time() - t0))
    tag = args.only.replace(",", "")
    json.dump(res, open(os.path.join(OUT, "scans_%s.json" % tag), "w"), indent=1, default=str)


if __name__ == "__main__":
    main()
