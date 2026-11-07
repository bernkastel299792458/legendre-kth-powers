"""
Coordinator request (k ~ 30-50): KLN-type density constants for LOWER sigma.

Tier "refereed" (form 'JY52'):
    N(s,T) <= C1 T^{8(1-s)/3} (log T)^{5-2s} + C2 log^2 T,   T >= H0 = 3e12,
    = KLN18 Lemma 4.14 (eq. 4.71) with k = 1 exactly as Johnston--Yang ran it:
      original KLN Lemma 4.3 (Ramare, Math. Comp. 85 (2016) Lemma 5.5: b4 = 0.529, tau^2 form),
      H = H0 - 1, H0 = 3e12 (Platt--Trudgian), eta = 0.25618, mu = 1.23623,
      C8 via Cully-Hugill--Trudgian Thm 2 (Ramanujan J. 56 (2021)),
      a1 = 0.618 (Hiary--Patel--Yang, JNT 256 (2024)), a2 = 2.8245 (zeta_half_max.py);
      alpha, delta, d optimised.  NO RZA, NO Theorem R.
    Reported C1, C2 are KLN's A = calC1/(2 pi d), B = calC2/(2 pi d) (= JY's C1(s), C2(s)).
Tier "uses Theorem R b4 = 0.5161" (form 'B119'):
    N <= A T^{8(1-s)/3} (log T)^{6-4s} + B log^2 T  (corrected CS (119); variant "CS").

Intervals: log calC1 and calC2 are AFFINE in sigma for fixed parameters, so for a row
[s1,s2] we take C1 = max(C1(s1), C1(s2)), C2 = max(C2(s1), C2(s2)) -- exact, no monotonicity
assumption (we also report whether C1 increases / C2 decreases, as JY claim).
Point rows (sigma_lo = sigma_hi) are valid at that sigma only.

Run: python -I run_low_sigma.py > run_low_sigma_out.txt     (writes kln_rows_low_sigma.csv)
"""
import sys, os, math, csv
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from flint import arb, ctx
import scipy.optimize as so
from cs_kln import KLN

ctx.prec = 128
H0 = arb("3e12")
ETA, MU = arb("0.25618"), arb("1.23623")      # JY: mu = 1.23623; eta as KLN (min C7)
ETA_B, MU_B = arb("0.25345"), arb("1.2363")    # CS (B119) choices
fails = []
out_rows = []


def roundup(x, nd=3):
    u = float(x.upper())
    v = math.ceil(u * 10 ** nd - 1e-9) / 10 ** nd
    while not bool(arb(repr(v)) >= x):
        v += 10 ** -nd
    return "%.*f" % (nd, v)


def model(form, a1="0.618", a2="2.8245"):
    if form == "JY52":
        return KLN(H0, a1=arb(a1), a2=arb(a2), b4=arb("0.529"), variant="KLN")
    return KLN(H0, a1=arb(a1), a2=arb(a2), b4=arb("0.5161"), variant="CS")


def evalrow(m, form, al, de, d, s1, s2):
    eta, mu = (ETA, MU) if form == "JY52" else (ETA_B, MU_B)
    c1_s2, c2_s1, ch = m.AB(al, d, de, eta, mu, s1, s2, c8mode="CT19")   # AB(.., s1, s2) = (C1(s2), C2(s1))
    c1_s1, c2_s2, ch2 = m.AB(al, d, de, eta, mu, s2, s1, c8mode="CT19")  # = (C1(s1), C2(s2))
    ch.update({k + "#": v for k, v in ch2.items()})
    if form == "B119":
        ch["eps<=0.0227"] = bool(2 * de / H0.log() <= arb("0.0227"))
    return c1_s2.max(c1_s1), c2_s1.max(c2_s2), ch, (c1_s1, c1_s2, c2_s1, c2_s2)


def optimise(m, form, s1, s2, x0):
    dmax = 0.32608 if form == "B119" else 5.0
    ctx.prec = 53

    def f(x):
        al, de, d = x
        if al <= 0.005 or de <= 0.05 or de > dmax or d <= 0.05:
            return 1e9
        try:
            a, b, ch, _ = evalrow(m, form, arb(al), arb(de), arb(d), s1, s2)
            return float(a.mid()) if all(ch.values()) else 1e9
        except Exception:
            return 1e9
    r = so.minimize(f, x0, method="Nelder-Mead", options=dict(xatol=1e-5, fatol=1e-6, maxiter=600))
    ctx.prec = 128
    return [arb(str(round(float(v), 4))) for v in r.x]


# ---------------------------------------------------------------- reproduction check
print("=" * 100)
print("Reproduction: Johnston-Yang Table 3 (a1=0.77, a2=3.161, H0=3000175332800, CT19, mu=1.23623)")
mjy = KLN(arb(3000175332800), a1=arb("0.77"), a2=arb("3.161"), b4=arb("0.529"), variant="KLN")
for s, d, al, de, C1, C2 in [("0.98", "0.3333", "0.0633", "0.3101", "16.281", "2.231"),
                             ("0.99", "0.3329", "0.0586", "0.3103", "16.848", "2.150")]:
    a, b, ch = mjy.AB(arb(al), arb(d), arb(de), ETA, MU, arb(s), arb(s), c8mode="CT19")
    print("   sigma=%s: C1=%s (JY %s)  C2=%s (JY %s)  checks=%s" % (s, a.str(7, radius=False), C1,
          b.str(6, radius=False), C2, all(ch.values())))
    # reproduction = agreement within one unit of the last printed digit; whether the printed
    # value is >= the computed one (i.e. a valid upper bound) is reported separately
    print("      printed >= computed?  C1: %s   C2: %s" % (bool(a <= arb(C1)), bool(b <= arb(C2))))
    if not (bool(abs(a - arb(C1)) < arb("0.001")) and bool(abs(b - arb(C2)) < arb("0.001"))):
        fails.append(("JY repro", s))
# same rows with our inputs (a1 = 0.618, H0 = 3e12)
m = model("JY52")
for s in ("0.98", "0.99"):
    al, de, d = optimise(m, "JY52", arb(s), arb(s), [0.063, 0.31, 0.333])
    a, b, ch, _ = evalrow(m, "JY52", al, de, d, arb(s), arb(s))
    print("   ours (a1=0.618, H0=3e12) sigma=%s: C1=%s C2=%s" % (s, a.str(6, radius=False), b.str(5, radius=False)))

# ---------------------------------------------------------------- JY52, refereed
grid = [arb(850 + 5 * i) / 1000 for i in range(27)]          # 0.850 ... 0.980
gs = ["%.3f" % (0.850 + 0.005 * i) for i in range(27)]
for form in ("JY52", "B119"):
    m = model(form)
    tier = "refereed" if form == "JY52" else "uses Theorem R b4=0.5161"
    print("=" * 100)
    print("form %s, tier %s, T >= 3e12" % (form, tier))
    if form == "JY52":
        pts = list(range(27))
        rows = [(i, i + 1) for i in range(26)]
    else:
        pts = [i for i in range(27) if 0.8999 < float(gs[i]) < 0.9376]
        rows = [(i, i + 1) for i in pts if i + 1 < 27 and float(gs[i + 1]) <= 0.9351] + [("0.935", "0.9375"), ("0.90625", "0.9375"), ("0.90", "0.9375")]
    x = [0.11, 0.304, 0.334] if form == "JY52" else [0.1, 0.324, 0.312]
    # point rows
    for i in pts:
        s = grid[i]
        x0 = [0.0551 + 0.464 * (1 - float(gs[i])), float(x[1]), float(x[2])]
        al, de, d = optimise(m, form, s, s, x0)
        C1, C2, ch, _ = evalrow(m, form, al, de, d, s, s)
        ok = all(ch.values())
        if not ok:
            fails.append((form, gs[i]))
        print("   sigma=%s          C1<=%-8s C2<=%-7s (alpha,delta,d)=(%s,%s,%s) ok=%s" % (
            gs[i], roundup(C1), roundup(C2), al.str(4, radius=False), de.str(4, radius=False), d.str(4, radius=False), ok))
        out_rows.append(dict(sigma_lo=gs[i], sigma_hi=gs[i], T0="3e12", C1=roundup(C1), C2=roundup(C2), form=form,
                             tier=tier, notes="point value; alpha=%s delta=%s d=%s" % (
                                 al.str(4, radius=False), de.str(4, radius=False), d.str(4, radius=False))))
    # interval rows
    for r in rows:
        if isinstance(r[0], int):
            s1s, s2s = gs[r[0]], gs[r[1]]
        else:
            s1s, s2s = r
        s1, s2 = arb(s1s), arb(s2s)
        x0 = [0.0551 + 0.464 * (1 - float(s2s)), float(x[1]), float(x[2])]
        al, de, d = optimise(m, form, s1, s2, x0)
        C1, C2, ch, (c1_s1, c1_s2, c2_s1, c2_s2) = evalrow(m, form, al, de, d, s1, s2)
        ok = all(ch.values())
        if not ok:
            fails.append((form, s1s, s2s))
        mono = "C1 incr=%s, C2 decr=%s" % (bool(c1_s2 >= c1_s1), bool(c2_s1 >= c2_s2))
        print("   [%s,%s]  C1<=%-8s C2<=%-7s (alpha,delta,d)=(%s,%s,%s) %s ok=%s" % (
            s1s, s2s, roundup(C1), roundup(C2), al.str(4, radius=False), de.str(4, radius=False), d.str(4, radius=False), mono, ok))
        extra = "; eps=2delta/logH0=%s" % (2 * de / H0.log()).str(4, radius=False) if form == "B119" else ""
        out_rows.append(dict(sigma_lo=s1s, sigma_hi=s2s, T0="3e12", C1=roundup(C1), C2=roundup(C2), form=form,
                             tier=tier, notes="interval: C1=max(C1(lo),C1(hi)), C2=max(C2(lo),C2(hi)); %s; alpha=%s delta=%s d=%s%s" % (
                                 mono, al.str(4, radius=False), de.str(4, radius=False), d.str(4, radius=False), extra)))

p = os.path.join(os.path.dirname(os.path.abspath(__file__)), "kln_rows_low_sigma.csv")
with open(p, "w", newline="", encoding="utf8") as fh:
    w = csv.DictWriter(fh, fieldnames=["sigma_lo", "sigma_hi", "T0", "C1", "C2", "form", "tier", "notes"])
    w.writeheader()
    for r in out_rows:
        w.writerow(r)
print("wrote", p, len(out_rows), "rows")
print("FAILS:", fails)
sys.exit(1 if fails else 0)
