"""
rza_euler.py -- independent Arb recomputation of every finite Euler product / prime sum over
p <= M = 10^8 that the paper hard-codes ("PRECISION 10^8" constants), plus the correct
version of the one product whose printed factor we believe is wrong (P0_LX).

Each factor is ALSO recomputed from the generic definitions of Theorem 4.1 / 4.2
(H_{f'}(0), Hbar_{f'}(-delta), P_alpha, T_f) applied to the local factor f(p); the script
checks at many primes that the paper's simplified closed forms equal the generic ones
(they do, except P0_LX).

Output: out/euler_products.json  (mid, rad as decimal strings)
Run:    python -I rza_euler.py      (~1-3 min with 16 processes)
"""
import os, sys, json, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
from rza_common import OUTDIR as OUT
MAXP = 10 ** 8

NAMES = ["P1_M", "P1_delta2_M", "P2", "P2_delta", "P3", "P3_spec", "P1x", "P1x_delta",
         "P0_LX_paperformula", "P0_LX_true", "P1_LX", "APROD_all", "ASUM_all", "PPdelta_all",
         "Sumx_p3", "ASumx_p3"]


def primes_upto(n):
    s = np.ones(n + 1, dtype=bool)
    s[:2] = False
    s[4::2] = False
    for i in range(3, int(n ** 0.5) + 1, 2):
        if s[i]:
            s[i * i::2 * i] = False
    return np.nonzero(s)[0]


def factors(p, flint_mod=None):
    """return dict name -> factor (products) or term (sums) at prime p (python int), in arb"""
    from flint import arb
    from rza_common import XI
    P = arb(p)
    sp = P.sqrt()
    lp = P.log()
    px = (XI * lp).exp()
    r712 = (lp * 7 / 12).exp()
    r76 = (lp * 7 / 6).exp()
    r16 = (lp / 6).exp()
    r23 = (lp * 2 / 3).exp()
    r43 = (lp * 4 / 3).exp()
    r116 = (lp * 11 / 6).exp()
    d = {}
    odd = p > 2
    if odd:
        d["P1_M"] = 1 + (2 * P - sp - 1) / (P ** 2 * (sp - 1))
        d["P1_delta2_M"] = 1 + (2 * r712 + sp + 1) / (r76 * (sp - 1))
        d["P2"] = 1 + (px * sp + P - px - px / sp) / (P ** 2 * (px - 1))
        d["P2_delta"] = 1 + (px * r16 + px + r23 + px / sp) / (r43 * (px - 1))
        d["P3"] = 1 + (2 * P * px - 2 * px ** 2 - P + px ** 2 / P) / (P ** 2 * (px - 1) ** 2)
        d["P3_spec"] = 1 + (2 * px - px ** 2 / P - 1) / ((px - 1) ** 2 * (sp - 1))
        d["P1x"] = 1 + (P - sp - 1) / (P ** 2 * sp)
        d["P1x_delta"] = 1 + (r23 + sp + 1) / r116
        d["P0_LX_paperformula"] = 1 + (P ** 2 - 2 * P * px - px) / (P ** 3 * (px - 1))
        d["P0_LX_true"] = 1 + (P ** 2 - 2 * P * px + px) / (P ** 3 * (px - 1))
        d["P1_LX"] = 1 + (P / px - 1) / ((P / px) * (px - 1) * (sp - 1))
        d["Sumx_p3"] = -(P ** 2 - 3 * P * px + 2 * px) * lp / (((P - 1) * px + P ** 2 * (px - 1)) * (P - 1))
        d["ASumx_p3"] = -(2 * P ** 2 * px - 3 * P * px ** 2 - P ** 2 + 2 * px ** 2) * lp / (
            (P ** 2 * px ** 2 - 2 * P ** 2 * px + P * px ** 2 + P ** 2 - px ** 2) * (P - 1))
    d["APROD_all"] = 1 - 2 / P ** 2 + 1 / P ** 3
    d["ASUM_all"] = (3 * P - 2) * lp / ((P - 1) * (P ** 2 + P - 1))
    d["PPdelta_all"] = 1 + 1 / (P * sp - P)
    return d


SUMS = {"ASUM_all", "Sumx_p3", "ASumx_p3"}


def generic(p):
    """same quantities from the generic definitions (Thm 4.1/4.2) applied to f(p)"""
    from flint import arb
    from rza_common import XI
    P = arb(p)
    sp = P.sqrt()
    px = (XI * P.log()).exp()
    lp = P.log()
    phi_half = sp - 1
    phi_xi = px - 1
    out = {}
    H0 = lambda f: 1 - (1 - f) / P - f / P ** 2                    # alpha=0, s=0
    Hb = lambda f, dl: 1 + abs(1 - f) / (P.log() * (1 - dl)).exp() + abs(f) / (P.log() * (2 - 2 * dl)).exp()
    # Aux1: f = phi(p)/phi_{1/2}(p)^2
    f = (P - 1) / phi_half ** 2
    out["P1_M"] = H0(f); out["P1_delta2_M"] = Hb(f, arb(5) / 12)
    # Aux2: f = phi(p)/p * sqrt p/phi_half * p^xi/phi_xi
    f = (P - 1) / P * sp / phi_half * px / phi_xi
    out["P2"] = H0(f); out["P2_delta"] = Hb(f, arb(1) / 3)
    # Aux3: f = phi(p)/p * (p^xi/phi_xi)^2 ; Thm 4.2[B] alpha=0
    f = (P - 1) / P * (px / phi_xi) ** 2
    out["P3"] = 1 - (P - f * P + f) / P ** 2
    out["P3_spec"] = 1 + abs(f - 1) / (sp - 1)
    # auxnu2 (h=1): f = phi(p)/p^{3/2} * sqrt p/phi_half ; alpha = 1/2
    f = (P - 1) / P ** 1 / phi_half
    fa = f * sp
    out["P1x"] = 1 - (1 - fa) / P - fa / P ** 2
    out["P1x_delta"] = 1 + abs(1 - fa) / (lp * 2 / 3).exp() + abs(fa) / (lp * 4 / 3).exp()
    # auxf2: f = phi(p)/p^2 * p^xi/phi_xi ; alpha = 1 : (1+f)(1-1/p) and P_1, T_f
    f = (P - 1) / P ** 2 * px / phi_xi
    out["P0_LX_true"] = (1 + f) * (1 - 1 / P)
    out["P1_LX"] = 1 + abs(f * P - 1) / (sp - 1)
    out["Sumx_p3"] = (1 - (P - 2) * f) * lp / ((f + 1) * (P - 1))
    # auxf22: f = phi(p)/p^2 (p^xi/phi_xi)^2
    f2 = (P - 1) / P ** 2 * (px / phi_xi) ** 2
    out["ASumx_p3"] = (1 - (P - 2) * f2) * lp / ((f2 + 1) * (P - 1))
    out["P3_from_K2"] = (1 + f2) * (1 - 1 / P)
    out["P3s_from_K2"] = 1 + abs(f2 * P - 1) / (sp - 1)
    return out


def worker(args):
    ps, prec = args
    from flint import arb, ctx
    import rza_common
    ctx.prec = prec
    acc = {k: (arb(0) if k in SUMS else arb(1)) for k in NAMES}
    for p in ps.tolist():  # noqa
        d = factors(p)
        for k, v in d.items():
            if k in SUMS:
                acc[k] += v
            else:
                acc[k] *= v
    return {k: (v.mid().str(45, radius=False), v.rad().str(6, radius=False)) for k, v in acc.items()}


def main():
    t0 = time.time()
    from flint import arb, ctx
    ctx.prec = 160
    # 1. identity check: paper closed forms vs generic definitions
    bad = []
    for p in [3, 5, 7, 11, 13, 101, 1009, 99991, 10 ** 8 - 11]:
        a, g = factors(p), generic(p)
        for k in g:
            kk = {"P3_from_K2": "P3", "P3s_from_K2": "P3_spec"}.get(k, k)
            if not (a[kk] - g[k]).abs_upper() < arb(10) ** -30:
                bad.append((p, k, a[kk].str(12), g[k].str(12)))
        pf, pt = a["P0_LX_paperformula"], a["P0_LX_true"]
        if p < 20:
            print("  p=%d  P0_LX factor: printed formula %s   (1+f)(1-1/p) %s" % (p, pf.str(10), pt.str(10)))
    print("closed-form vs generic mismatches:", bad if bad else "none")
    # 2. products over p <= 1e8 (p >= 3 for the *_p3 / odd ones; all p for *_all)
    allp = primes_upto(MAXP)
    assert len(allp) == 5761455
    tasks = [(chunk, 128) for chunk in np.array_split(allp, 64)]
    with Pool(16) as pool:
        parts = pool.map(worker, tasks)
    res = {}
    for k in NAMES:
        tot = arb(0) if k in SUMS else arb(1)
        for part in parts:
            m, r = part[k]
            v = arb(m, r) + arb(0, "1e-40")
            tot = tot + v if k in SUMS else tot * v
        res[k] = tot
    os.makedirs(OUT, exist_ok=True)
    with open(os.path.join(OUT, "euler_products.json"), "w") as fh:
        json.dump({k: [v.mid().str(30, radius=False), (v.rad() + arb("1e-28")).str(5, radius=False)] for k, v in res.items()},
                  fh, indent=1)
    from rza_assembly import PAPER
    paper = {"P1_M": PAPER["P1_M"], "P1_delta2_M": PAPER["P1_delta2_M"], "P2": PAPER["P2"],
             "P2_delta": PAPER["P2_delta"], "P3": PAPER["P3"], "P3_spec": PAPER["P3_spec"],
             "P1x": PAPER["P1x"], "P1x_delta": PAPER["P1x_delta"], "P0_LX_paperformula": PAPER["P0_LX"],
             "P0_LX_true": PAPER["P0_LX"], "P1_LX": PAPER["P1_LX"], "APROD_all": PAPER["APROD"],
             "ASUM_all": PAPER["ASUM_p"], "PPdelta_all": PAPER["PPdelta"], "Sumx_p3": PAPER["Sumx_p3"],
             "ASumx_p3": PAPER["ASumx_p3"]}
    print("%-20s %-34s %-16s %s" % ("constant", "Arb, p<=1e8", "paper", "paper - Arb"))
    for k in NAMES:
        v = res[k]
        pv = arb(paper[k])
        print("%-20s %-34s %-16s %s" % (k, v.str(20, radius=True)[:34], paper[k], (pv - v).str(3, radius=False)))
    print("time %.1f s" % (time.time() - t0))


if __name__ == "__main__":
    main()
