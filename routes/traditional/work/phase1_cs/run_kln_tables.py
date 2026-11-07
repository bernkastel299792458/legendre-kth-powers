"""
(B): CS eq. (119) / Table 4 (sec. 6, 'Appendix') -- reproduction and correction.

Part 1. Reproduce published tables with our Arb implementation of KLN Lemma 4.14
        (validates cs_kln.py): KLN Table 1, Johnston--Yang Table 3, CS Table 4.
Part 2. Corrected CS Table 4 rows for sigma >= 0.9375:
        - correct log-factor  e^{4d loglogH0/logH0}  (variant "CS"),
        - b4 = 0.5936 (Ramare--Zuniga Alterman arXiv:2603.25961v3 Thm 1.2,
          10^12 <= X < 10^16, eps <= 1/25; 0.5103 for 10^16<=X<10^33, eps<=1/50;
          0.51 for X >= 10^33, eps <= 1/25),
        - a1 = 0.618 (Hiary--Patel--Yang, JNT 256 (2024), t >= 3), a2 = 2.8245
          (>= max_{|t|<=3}|zeta(1/2+it)| + 6 a1/e, zeta_half_max.py),
        - C8 via KLN (3.13) [our proof: d^2 <= d_4] and via CT19 Thm 2,
        - parameters re-optimised (floats), final values in Arb, rounded up.
Run:  python -I run_kln_tables.py  > run_kln_tables_out.txt
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from flint import arb, ctx
from cs_kln import KLN, PI
import math

ctx.prec = 128
fails = []


def chk(tag, computed, printed, mode="bound"):
    """mode 'bound': printed value must be >= computed (a claimed upper bound);
    mode 'repro': report agreement up to rounding of the last printed digit."""
    if mode == "bound":
        ok = bool(computed <= arb(printed))
        st = "OK (printed >= computed)" if ok else "EXCEEDS printed"
    else:
        nd = len(printed.split(".")[1]) if "." in printed else 0
        diff = computed - arb(printed)
        ok = bool(abs(diff) <= arb(10) ** (-nd) / 2 + arb(10) ** (-nd - 3))
        st = "agrees to rounding" if ok else "DIFFERS by %s" % diff.str(3, radius=False)
    print("   %-10s computed %-12s printed %-8s %s" % (tag, computed.str(6, radius=False), printed, st))
    return ok


print("=" * 90)
print("PART 1a. KLN (arXiv:2101.12263v1) Table 1, original formulas (H0=3.0610046e10, a1=.63, b4=.529)")
m = KLN(arb("3.0610046e10"))
for s, mu, al, de, d, A, B in [("0.97", "1.245", "0.069", "0.3030", "0.332", "15.850", "2.609"),
                              ("0.98", "1.245", "0.064", "0.3030", "0.331", "16.544", "2.532"),
                              ("0.99", "1.245", "0.060", "0.3030", "0.331", "17.253", "2.446")]:
    a, b, c = m.AB(arb(al), arb(d), arb(de), arb("0.25618"), arb(mu), arb(s), arb(s))
    print(" sigma=%s" % s, c)
    chk("A", a, A, "repro"); chk("B", b, B, "repro")

print("PART 1b. Johnston-Yang (JMAA 527 (2023)) Table 3 (H0=3000175332800, a1=.77, a2=3.161, CT19 for (3.13))")
m = KLN(arb(3000175332800), a1=arb("0.77"), a2=arb("3.161"))
for s, d, al, de, C1, C2 in [("0.98", "0.3333", "0.0633", "0.3101", "16.281", "2.231"),
                             ("0.99", "0.3329", "0.0586", "0.3103", "16.848", "2.150"),
                             ("1", "0.3325", "0.0539", "0.3105", "17.418", "2.069")]:
    a, b, c = m.AB(arb(al), arb(d), arb(de), arb("0.25618"), arb("1.23623"), arb(s), arb(s), c8mode="CT19")
    print(" sigma=%s" % s)
    chk("C1", a, C1, "repro"); chk("C2", b, C2, "repro")

CS_T4 = [  # sig1, sig2, A, B, alpha, delta, d   (CS Table 4, rows used here)
    ("0.90625", "0.93750", "12.88", "2.807", "0.086", "0.324", "0.338"),
    ("0.93750", "0.96875", "14.81", "2.558", "0.070", "0.325", "0.337"),
    ("0.96875", "0.97500", "15.21", "2.301", "0.067", "0.325", "0.337"),
    ("0.97500", "0.98125", "15.62", "2.249", "0.064", "0.325", "0.337"),
    ("0.98125", "0.98750", "16.04", "2.204", "0.061", "0.325", "0.336"),
    ("0.98750", "0.99375", "16.46", "2.153", "0.058", "0.325", "0.336"),
    ("0.99375", "1.00000", "16.89", "2.101", "0.056", "0.325", "0.336"),
]
ETA, MU = arb("0.25345"), arb("1.2363")

print("PART 1c. CS Table 4.  Text says H0=3.0610046e10; only the following reproduces it:")
print("         H0=3e12, a1=.63, a2=2.851, b4=0.54, CT19 for (3.13), KLN's (4.72) log-factor unchanged")
for H0s, var, c8 in (("3.0610046e10", "CS_literal", "KLN"), ("3e12", "CS_literal", "CT19")):
    m = KLN(arb(H0s), b4=arb("0.54"), variant=var)
    print(" -- H0=%s variant=%s C8=%s" % (H0s, var, c8))
    for s1, s2, A, B, al, de, d in CS_T4:
        a, b, c = m.AB(arb(al), arb(d), arb(de), ETA, MU, arb(s1), arb(s2), c8mode=c8)
        a1_, b1_, _ = m.AB(arb(al), arb(d), arb(de), ETA, MU, arb(s1), arb(s1), c8mode=c8)
        print("  [%s,%s]" % (s1, s2))
        chk("A(sig2)", a.max(a1_), A); chk("B(sig1)", b, B)

print("=" * 90)
print("PART 2. Corrected (B).  N(s,T) <= A T^{8(1-s)/3} (log T)^{6-4s} + B log^2 T, T >= 3e12, s in [s1,s2]")
H0 = arb("3e12")
A1C, A2C = arb("0.618"), arb("2.8245")


def model(b4=arb("0.5936"), var="CS"):
    return KLN(H0, a1=A1C, a2=A2C, b4=b4, variant=var)


def AB_row(mdl, al, de, d, s1, s2, c8="CT19"):
    a2, b1, c = mdl.AB(al, d, de, ETA, MU, s1, s2, c8mode=c8)
    a1, _, _ = mdl.AB(al, d, de, ETA, MU, s1, s1, c8mode=c8)   # log C1 is affine in s: max of ends
    return a2.max(a1), b1, c


def optimise(mdl, s1, s2, x0):
    import scipy.optimize as so
    ctx.prec = 53

    def f(x):
        al, de, d = x
        if al <= 0.01 or de <= 0.05 or de > 0.368 or d <= 0.05:
            return 1e9
        try:
            a, b, c = AB_row(mdl, arb(al), arb(de), arb(d), s1, s2)
            if not all(c.values()):
                return 1e9
            return float(a.mid())
        except Exception:
            return 1e9
    r = so.minimize(f, x0, method="Nelder-Mead", options=dict(xatol=1e-5, fatol=1e-6, maxiter=400))
    ctx.prec = 128
    return r.x


def roundup(x, nd=3):
    """decimal string >= x with nd decimals (x an arb ball)."""
    u = float(x.upper()) if hasattr(x, "upper") else float(x)
    v = math.ceil(u * 10 ** nd - 1e-12) / 10 ** nd
    while not bool(arb(repr(v)) >= x):
        v += 10 ** -nd
    return "%.*f" % (nd, v)


rows_out = []
for s1s, s2s, A, B, al, de, d in CS_T4[1:]:
    s1, s2 = arb(s1s), arb(s2s)
    print(" row [%s,%s]   paper: A=%s B=%s (alpha,delta,d)=(%s,%s,%s)" % (s1s, s2s, A, B, al, de, d))
    # (i) paper parameters, only the log-factor corrected (b4 = 0.54 as in paper)
    m054 = model(b4=arb("0.54"))
    a, b, c = AB_row(m054, arb(al), arb(de), arb(d), s1, s2)
    print("   (i)  log-factor corrected, b4=0.54, a1=.618:     A=%s B=%s" % (a.str(6, radius=False), b.str(5, radius=False)))
    # (ii) + b4 = 0.5936
    mc = model()
    a, b, c = AB_row(mc, arb(al), arb(de), arb(d), s1, s2)
    print("   (ii) + b4=0.5936 (RZA v3):                      A=%s B=%s" % (a.str(6, radius=False), b.str(5, radius=False)))
    # (iii) re-optimised
    x = optimise(mc, s1, s2, [float(al), float(de), float(d)])
    alr, der, dr = [arb(str(round(float(v), 4))) for v in x]
    a, b, c = AB_row(mc, alr, der, dr, s1, s2)
    ak, bk, ck = AB_row(mc, alr, der, dr, s1, s2, c8="KLN")
    okeps = bool(2 * der / H0.log() <= arb(1) / 25) and bool(der <= arb("0.368"))
    print("   (iii) re-optimised (alpha,delta,d)=(%s,%s,%s): A=%s B=%s [B with KLN(3.13): %s]  checks=%s eps_ok=%s"
          % (alr.str(4, radius=False), der.str(4, radius=False), dr.str(4, radius=False),
             a.str(6, radius=False), b.str(5, radius=False), bk.str(5, radius=False), all(c.values()), okeps))
    if not (all(c.values()) and okeps):
        fails.append(("row", s1s))
    rows_out.append((s1s, s2s, roundup(a), roundup(b), roundup(bk), alr.str(4, radius=False),
                     der.str(4, radius=False), dr.str(4, radius=False)))

print("-" * 90)
print("CORRECTED TABLE (B), T >= 3e12 (b4=0.5936, a1=0.618, a2=2.8245, eta=0.25345, mu=1.2363, H=H0-1, k=1)")
print(" sig1     sig2     A        B(CT19)  B(KLN3.13)  alpha   delta   d")
for r in rows_out:
    print(" %s  %s  %-8s %-8s %-10s  %s  %s  %s" % r)
print("=" * 90)
print("PART 3. Extra rows for the project and larger T0 (KLN with H0 := T0 >= H = 3e12 - 1)")


def b4_for(X0, delta):
    assert bool(2 * delta / X0.log() <= arb(1) / 25)
    if bool(X0 < arb(10) ** 16):
        assert bool(2 * delta / (arb(10) ** 16).log() <= arb(1) / 50)
        return arb("0.5936")
    assert bool(2 * delta / X0.log() <= arb(1) / 50)
    return arb("0.5103") if bool(X0 < arb(10) ** 33) else arb("0.51")


for T0s in ("3e12", "e30", "e32", "e35", "1e16"):
    T0 = arb(T0s[1:]).exp() if T0s.startswith("e") else arb(T0s)
    for s1s, s2s in (("0.98", "0.99"), ("0.98", "0.985"), ("0.985", "0.99"), ("0.99", "1")):
        s1, s2 = arb(s1s), arb(s2s)
        de0 = arb("0.3253")
        mdl = KLN(T0, a1=A1C, a2=A2C, b4=b4_for(T0, de0), variant="CS", H=arb("3e12") - 1)
        x = optimise(mdl, s1, s2, [0.0608, 0.3253, 0.312])
        alr, der, dr = [arb(str(round(float(v), 4))) for v in x]
        mdl = KLN(T0, a1=A1C, a2=A2C, b4=b4_for(T0, der), variant="CS", H=arb("3e12") - 1)
        a, b, cc = AB_row(mdl, alr, der, dr, s1, s2)
        ok = all(cc.values())
        if not ok:
            fails.append(("P3", T0s, s1s))
        print(" T>=%-5s [%s,%s] b4=%s (alpha,delta,d)=(%s,%s,%s): A<=%s B<=%s checks=%s" % (
            T0s, s1s, s2s, mdl.b4.str(4, radius=False), alr.str(4, radius=False), der.str(4, radius=False),
            dr.str(4, radius=False), roundup(a), roundup(b), ok))
print("FAILS:", fails)
sys.exit(1 if fails else 0)
