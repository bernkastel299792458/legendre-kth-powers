"""
Follow-up (coordinator request): recompute the corrected CS constants with the repaired
b4 = 0.5161 (work/audit_rza/repair/, Theorem R, Helfgott-free version:
S_eps(X) <= 0.5161 for X >= 3e12 and 0 < eps <= 0.0227; OWN LEMMA, NOT YET REVIEWED).
RZA Thm 1.2 (b4 = 0.5936) fails as proved (work/audit_rza/REPORT.md).

CS Lemma 7 is applied with X = T >= T0 (h = k = 1) at sigma = 1 + delta/log X, using
    S_eps(X) with eps = 2 delta/log X  (sum over n^{-(2 sigma - 1)})  and  eps = delta/log X.
Both are <= 2 delta/log T0, so the condition is  2 delta / log T0 <= 0.0227, i.e.
delta <= 0.01135 log T0  (= 0.32609 for T0 = 3e12).  Enforced (in Arb) for every row.

Outputs: cs_rows_b4_05161.csv  and  run_b4_05161_out.txt (stdout).
Run: python -I run_b4_05161.py > run_b4_05161_out.txt
"""
import sys, os, math, csv
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from flint import arb, ctx
import scipy.optimize as so
from cs_kln import KLN
import cs_thm1 as c

ctx.prec = 128
B4 = arb("0.5161")
EPS_MAX = arb("0.0227")
H_RH = arb("3e12")
ETA, MU = arb("0.25345"), arb("1.2363")
A1C, A2C = arb("0.618"), arb("2.8245")
fails = []
rows_csv = []


def roundup(x, nd):
    u = float(x.upper())
    v = math.ceil(u * 10 ** nd - 1e-9) / 10 ** nd
    while not bool(arb(repr(v)) >= x):
        v += 10 ** -nd
    return "%.*f" % (nd, v)


def eps_ok(delta, T0):
    """2 delta/log X <= 0.0227 for all X >= T0, and delta/log X (smaller) too; eps > 0."""
    return bool(delta > 0) and bool(2 * delta / T0.log() <= EPS_MAX)


def delta_max(T0):
    return float((EPS_MAX * T0.log() / 2).lower())


# ---------------------------------------------------------------- (B) / eq. (119)
def B_AB(T0, al, de, d, s1, s2, c8="CT19"):
    m = KLN(T0, a1=A1C, a2=A2C, b4=B4, variant="CS", H=H_RH - 1)
    a2_, b1_, chk = m.AB(al, d, de, ETA, MU, s1, s2, c8mode=c8)
    a1_, _, chk1 = m.AB(al, d, de, ETA, MU, s1, s1, c8mode=c8)
    chk.update({k + "@s1": v for k, v in chk1.items()})
    return a2_.max(a1_), b1_, chk


def B_opt(T0, s1, s2, x0):
    dm = delta_max(T0)
    ctx.prec = 53

    def f(x):
        al, de, d = x
        if al <= 0.01 or de <= 0.05 or de > dm - 1e-6 or d <= 0.05:
            return 1e9
        try:
            a, b, ch = B_AB(T0, arb(al), arb(de), arb(d), s1, s2)
            return float(a.mid()) if all(ch.values()) else 1e9
        except Exception:
            return 1e9
    r = so.minimize(f, x0, method="Nelder-Mead", options=dict(xatol=1e-5, fatol=1e-6, maxiter=500))
    ctx.prec = 128
    return [arb(str(round(float(v), 4))) for v in r.x]


B_SIG = [("0.93750", "0.96875"), ("0.96875", "0.97500"), ("0.97500", "0.98125"), ("0.98125", "0.98750"),
         ("0.98750", "0.99375"), ("0.99375", "1.00000"),
         ("0.98", "0.985"), ("0.985", "0.99"), ("0.99", "1"), ("0.98", "0.99"), ("0.98", "1")]
T0S = [("3e12", arb("3e12")), ("e30", arb(30).exp()), ("e32", arb(32).exp()), ("e35", arb(35).exp())]

print("=" * 100)
print("(B) eq.(119) corrected, b4 = 0.5161:  N <= A T^{8(1-s)/3}(log T)^{6-4s} + B log^2 T,  T >= T0")
print("    k=1, H=3e12-1, eta=0.25345, mu=1.2363, a1=0.618, a2=2.8245, correct log-factor, C8 via CT19")
x0 = [0.0608, 0.3253, 0.3120]
for T0n, T0 in T0S:
    print("-- T0 = %s   (delta_max for eps <= 0.0227: %.5f)" % (T0n, delta_max(T0)))
    for s1s, s2s in B_SIG:
        s1, s2 = arb(s1s), arb(s2s)
        al, de, d = B_opt(T0, s1, s2, [0.0551 + 0.464 * (1 - float(s2)), min(0.3255, delta_max(T0) - 1e-3), 0.312])
        a, b, ch = B_AB(T0, al, de, d, s1, s2)
        ak, bk, chk = B_AB(T0, al, de, d, s1, s2, c8="KLN")
        ok = all(ch.values()) and eps_ok(de, T0)
        if not ok:
            fails.append(("B", T0n, s1s, s2s))
        epsv = 2 * de / T0.log()
        print("   [%s,%s]  A<=%s  B<=%s  (B with KLN(3.13): %s)  (alpha,delta,d)=(%s,%s,%s) eps_max=%s ok=%s" % (
            s1s, s2s, roundup(a, 3), roundup(b, 3), roundup(bk, 3), al.str(4, radius=False),
            de.str(4, radius=False), d.str(4, radius=False), epsv.str(5, radius=False), ok))
        rows_csv.append(dict(sigma_lo=s1s, sigma_hi=s2s, T0=T0n, A=roundup(a, 3), B=roundup(b, 3), form="B119",
                             b4="0.5161", notes="alpha=%s delta=%s d=%s eps<=%s; B_KLN313=%s; k=1 eta=0.25345 mu=1.2363 a1=0.618 a2=2.8245"
                             % (al.str(4, radius=False), de.str(4, radius=False), d.str(4, radius=False),
                                epsv.str(4, radius=False), roundup(bk, 3))))

# ---------------------------------------------------------------- (A) / Cor. 1
print("=" * 100)
print("(A) Cor. 1 corrected, b4 = 0.5161:  N <= B1 T^{3(1-s)/(2-s)}(log T)^{(7-5s)/(2-s)} + B2 log^2 T + B3 log T")
print("    Theorem 1 with H = H0 = H_RH = 3e12, h = 1, T0 as given; CSV columns A := B1, B := B2, B3 in notes")


def A_eval(T0, s1, s2, d, ka, de, lA, N):
    return c.thm1_constants(s1, s2, d, ka, de, c.rpow(arb(10), lA), T0=T0, H0=H_RH, b4=B4, K1N=N)


def A_opt(T0, s1, s2, x0):
    dm = delta_max(T0)
    ctx.prec = 53

    def f(x):
        d, ka, de, lA = x
        if d <= 0.05 or ka <= 0.005 or de <= 0.02 or de > dm - 1e-6 or lA < 10.0:
            return 1e9
        o = A_eval(T0, s1, s2, arb(d), arb(ka), arb(de), arb(lA), 800)
        return float(o["B1"].mid()) if all(o["hyp"].values()) else 1e9
    r = so.minimize(f, x0, method="Nelder-Mead", options=dict(xatol=1e-5, fatol=1e-5, maxiter=600))
    ctx.prec = 128
    return [arb(str(round(float(v), 4))) for v in r.x]


A_SIG = [("0.93750", "0.96875", [0.29, 0.09, 0.27, 11.42]), ("0.96875", "1.00000", [0.29, 0.07, 0.303, 11.46]),
         ("0.98", "1", [0.29, 0.07, 0.303, 11.46])]
for T0n, T0 in T0S:
    print("-- T0 = %s" % T0n)
    for s1s, s2s, x0 in A_SIG:
        s1, s2 = arb(s1s), arb(s2s)
        d, ka, de, lA = A_opt(T0, s1, s2, x0)
        o = A_eval(T0, s1, s2, d, ka, de, lA, 100000)
        ok = all(o["hyp"].values()) and eps_ok(de, T0)
        if not ok:
            fails.append(("A", T0n, s1s))
        epsv = 2 * de / T0.log()
        print("   [%s,%s]  B1<=%s B2<=%s B3<=%s  (d,kappa,delta,log10A0)=(%s,%s,%s,%s) eps_max=%s ok=%s" % (
            s1s, s2s, roundup(o["B1"], 2), roundup(o["B2"], 3), roundup(o["B3"], 2), d.str(4, radius=False),
            ka.str(4, radius=False), de.str(4, radius=False), lA.str(4, radius=False), epsv.str(5, radius=False), ok))
        rows_csv.append(dict(sigma_lo=s1s, sigma_hi=s2s, T0=T0n, A=roundup(o["B1"], 2), B=roundup(o["B2"], 3),
                             form="A", b4="0.5161",
                             notes="B1=A B2=B B3=%s; d=%s kappa=%s delta=%s log10A0=%s eps<=%s; H=H0=3e12 h=1"
                             % (roundup(o["B3"], 2), d.str(4, radius=False), ka.str(4, radius=False),
                                de.str(4, radius=False), lA.str(4, radius=False), epsv.str(4, radius=False))))

out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "cs_rows_b4_05161.csv")
with open(out, "w", newline="", encoding="utf8") as fh:
    w = csv.DictWriter(fh, fieldnames=["sigma_lo", "sigma_hi", "T0", "A", "B", "form", "b4", "notes"])
    w.writeheader()
    for r in rows_csv:
        w.writerow(r)
print("wrote", out, len(rows_csv), "rows")
print("FAILS:", fails)
sys.exit(1 if fails else 0)
