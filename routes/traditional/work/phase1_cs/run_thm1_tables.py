"""
(A): CS Corollary 1 / Table 1 (rows sigma >= 0.9375) -- reproduction and correction.

Part 1. Reproduce Table 1 rows [0.9375,0.96875] and [0.96875,1] from Theorem 1 with
        the paper's parameters and the paper's b4 = 0.54 (Lemma 7, private communication).
Part 2. Corrected rows: b4 = 0.5936 (Ramare--Zuniga Alterman arXiv:2603.25961v3, Thm 1.2:
        S_eps(X) <= 0.5936 for 10^12 <= X < 10^16, eps <= 1/25; <= 0.5103 for
        10^16 <= X < 10^33, eps <= 1/50; <= 0.51 for X >= 10^33, eps <= 1/25), both
        with the paper's parameters and with re-optimised (d, kappa, delta, log10 A0).
        RZA eps-conditions: eps = 2 delta/log X <= 1/25 for X >= 3e12 and <= 1/50 for
        X >= 10^16, i.e. delta <= 0.368 suffices.
Part 3. Same at larger T0 (Theorem 1 with H = H0 = H_RH, T0 > H_RH), for T >= T0.
Run:  python -I run_thm1_tables.py > run_thm1_tables_out.txt
"""
import sys, os, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from flint import arb, ctx
import cs_thm1 as c

ctx.prec = 128
N_RIG = 100000      # Riemann-sum resolution for K1 in final (claimed) values
fails = []


def roundup(x, nd):
    u = float(x.upper())
    v = math.ceil(u * 10 ** nd - 1e-9) / 10 ** nd
    while not bool(arb(repr(v)) >= x):
        v += 10 ** -nd
    return "%.*f" % (nd, v)


def b4_for(X0, delta):
    """RZA v3 Thm 1.2 constant valid for all X >= X0 (needs X0 >= 1e12)."""
    assert bool(X0 >= arb(10) ** 12)
    assert bool(2 * delta / X0.log() <= arb(1) / 25), "eps > 1/25"
    if bool(X0 < arb(10) ** 16):
        assert bool(2 * delta / (arb(10) ** 16).log() <= arb(1) / 50)
        return arb("0.5936")
    if bool(X0 < arb(10) ** 33):
        assert bool(2 * delta / X0.log() <= arb(1) / 50)
        return arb("0.5103")
    return arb("0.51")


print("=" * 90)
print("PART 1. Reproduction of Table 1 (b4 = 0.54 as in the paper), K1 by %d-step Riemann sums" % N_RIG)
for row in c.TABLE1:
    p, pr = c.row_params(row)
    o = c.thm1_constants(K1N=N_RIG, **p)
    print(" row [%s,%s]  hyp=%s" % (row[0], row[1], all(o["hyp"].values())))
    for k, pv in zip(("B1", "B2", "B3"), pr):
        ok = bool(o[k] <= pv)
        print("   %s computed %-12s printed %-6s %s" % (k, o[k].str(7, radius=False), pv.str(5, radius=False),
                                                     "OK (printed >= computed)" if ok else "EXCEEDS"))
        if not ok:
            fails.append((row[0], k))
    print("   K1 in [%s, %s]" % (o["K1lo"].str(8, radius=False), o["K1"].str(8, radius=False)))


def optimise(s1, s2, x0, T0=None, H0=None):
    import scipy.optimize as so
    ctx.prec = 53
    T0v = c.H_RH if T0 is None else T0

    def f(x):
        d, ka, de, lA = x
        if d <= 0.05 or ka <= 0.005 or de <= 0.02 or de > 0.368 or lA < 10.0:
            return 1e9
        try:
            b4 = b4_for(T0v, arb(de))
            o = c.thm1_constants(arb(s1), arb(s2), arb(d), arb(ka), arb(de), c.rpow(arb(10), arb(lA)),
                                 T0=T0, H0=H0, b4=b4, K1N=800)
            if not all(o["hyp"].values()):
                return 1e9
            return float(o["B1"].mid())
        except AssertionError:
            return 1e9
    r = so.minimize(f, x0, method="Nelder-Mead", options=dict(xatol=1e-5, fatol=1e-5, maxiter=600))
    ctx.prec = 128
    return r.x


corrected = []
print("=" * 90)
print("PART 2. Corrected rows, T >= H_RH = 3e12 (T0 = H0 = H = H_RH, h = 1)")
for row in c.TABLE1:
    p, pr = c.row_params(row)
    b4 = b4_for(c.H_RH, p["delta"])
    o = c.thm1_constants(b4=b4, K1N=N_RIG, **p)
    print(" row [%s,%s] paper params, b4=%s: B1=%s B2=%s B3=%s" % (row[0], row[1], b4.str(5, radius=False),
          o["B1"].str(6, radius=False), o["B2"].str(6, radius=False), o["B3"].str(6, radius=False)))
    x = optimise(row[0], row[1], [float(row[5]), float(row[6]), float(row[7]), float(row[8])])
    d, ka, de, lA = [arb(str(round(float(v), 4))) for v in x]
    b4 = b4_for(c.H_RH, de)
    o = c.thm1_constants(p["sig1"], p["sig2"], d, ka, de, c.rpow(arb(10), lA), b4=b4, K1N=N_RIG)
    ok = all(o["hyp"].values())
    if not ok:
        fails.append(("opt", row[0]))
    print("   re-optimised (d,kappa,delta,log10A0)=(%s,%s,%s,%s): B1=%s B2=%s B3=%s hyp=%s" % (
        d.str(4, radius=False), ka.str(4, radius=False), de.str(4, radius=False), lA.str(4, radius=False),
        o["B1"].str(6, radius=False), o["B2"].str(6, radius=False), o["B3"].str(6, radius=False), ok))
    corrected.append((row[0], row[1], roundup(o["B1"], 2), roundup(o["B2"], 3), roundup(o["B3"], 2),
                      d.str(4, radius=False), ka.str(4, radius=False), de.str(4, radius=False), lA.str(4, radius=False)))

print("-" * 90)
print("CORRECTED TABLE (A): N(s,T) <= B1 T^{3(1-s)/(2-s)} (log T)^{(7-5s)/(2-s)} + B2 log^2 T + B3 log T, T >= 3e12")
print(" sig1     sig2     B1      B2      B3      d       kappa   delta   log10A0")
for r in corrected:
    print(" %s  %s  %-7s %-7s %-7s %s  %s  %s  %s" % r)

print("=" * 90)
print("PART 3. Larger T0 (H = H0 = H_RH): constants valid for T >= T0; parameters re-optimised")
for row in c.TABLE1[1:]:
    p, pr = c.row_params(row)
    for lT0 in ("30", "32", "35", "37"):
        T0 = arb(lT0).exp()
        x = optimise(row[0], row[1], [float(row[5]), float(row[6]), float(row[7]), float(row[8])], T0=T0, H0=c.H_RH)
        d, ka, de, lA = [arb(str(round(float(v), 4))) for v in x]
        b4 = b4_for(T0, de)
        o = c.thm1_constants(p["sig1"], p["sig2"], d, ka, de, c.rpow(arb(10), lA), T0=T0, H0=c.H_RH,
                             b4=b4, K1N=N_RIG // 4)
        print(" row [%s,%s] T0=e^%s b4=%s (d,k,de,lA)=(%s,%s,%s,%s): B1<=%s  A3=%s A4=%s A5=%s hyp=%s" % (
            row[0], row[1], lT0, b4.str(4, radius=False), d.str(4, radius=False), ka.str(4, radius=False),
            de.str(4, radius=False), lA.str(4, radius=False), roundup(o["B1"], 2),
            o["A3"].str(5, radius=False), o["A4"].str(5, radius=False), o["A5"].str(5, radius=False),
            all(o["hyp"].values())))
print("FAILS:", fails)
sys.exit(1 if fails else 0)
