"""
F_grid.py -- independent float (mpmath, 30 digits) re-implementation of the repair's (R.10),
typed from the REPORT's formulas and its section-4 constant table (NOT from repair_bound.py),
evaluated on a dense grid of eps in (0, eps0].  Sanity check of the certificate's coding and of
the claim "sup at eps -> 0+", plus robustness variants.  Not a proof.
"""
import mpmath as mp
mp.mp.dps = 30

C = dict(  # rza variant, X0 = 3e12, eps0 = 0.0227, J = 68 (REPORT section 4 / repair_bound output)
    TH1="2.1205286", THx1="6.2404074", THx2="3.1885613", L1="0.13779107", L2="0.09686390",
    THx="1.8222265", THxxx="2.5878076", c1="0.71335777", mx="1.2941694", mm="0.5055381",
    LL2="0.06229665", W="0.42824951", G1="2.9682236", G2="1.1478998", S11="0.3328792894",
    S12="21924.0439", Wh="0.4323580916", G1h="2.8636589", G2h="1.1015508", S11h="0.3357949128",
    S12h="23491.9569", ax1="0.0160591", H1="0.010032", Clog="0.03", L0=str(12 * mp.log(10)), J="68", c="0.00205174")
HF = dict(C, TH2=None)
HF.update(dict(L1="0.1394021", L2="0.0682121", c1="0.62435411", mx="1.1724604", mm="0.5672307", LL2="0.0494549",
               H1="0.0144", Clog="0.0218353", L0=str(10 * mp.log(10)), J="69", c="0.00133055",
               S11="0.3329460886", S12="23212.2475", S11h="0.3358628805", S12h="24874.1009"))


def make_F(K, X0=mp.mpf("3e12"), e0=mp.mpf("0.0227"), g91=mp.mpf("9.1"), k4=1, k5=1, k6=1, kl=1):
    k = {a: (mp.mpf(b) if b is not None else None) for a, b in K.items()}
    Z = k["J"] + mp.mpf("0.9999")
    Tail0 = 2 * k["TH1"] / Z + 2 * mp.sqrt(2) * k["H1"] * k["L1"] / mp.sqrt(Z) + k["H1"] ** 2 * k["L2"]
    Bulk0 = k["W"] * (mp.log(2) + k["S11"]) + (k["G1"] * (1 + mp.sqrt(2)) + k["G2"] * k["S12"]) / mp.sqrt(X0)
    Bulk1 = k["Wh"] * (mp.log(2) + k["S11h"]) + (k["G1h"] * (1 + mp.sqrt(2)) + k["G2h"] * k["S12h"]) / mp.sqrt(X0)
    ax2 = mp.mpf(19) / 210
    L0 = k["L0"]

    def F(e):
        a = (5 + e * 2 ** e) / 2
        T1 = Z ** (-2 * e) * Tail0
        T2 = X0 ** (-e) * Bulk0 * (Bulk1 / Bulk0) ** (kl * e / e0)
        T3 = 2 * e * X0 ** (-e) * k["ax1"]
        T4 = 2 * e * 2 ** e * (mp.mpf("4.1") * k["THx"] + a * k["THxxx"]) * (
            mp.mpf("10.9") ** (-2 * e) * ax2 / mp.sqrt(mp.mpf("10.9")) + 47 ** (-2 * e) * (1 - ax2) / mp.sqrt(47))
        u = 2 * e * L0
        T5 = k["Clog"] * (2 * e * (k["mx"] - k["mm"]) / L0 + 2 * e * k["mm"] / mp.log(X0) + k["c1"] * u * mp.e1(u) / L0)
        cB = k["c"]
        Q = (a ** 2 * k["THx1"] + mp.mpf("8.2") * a * k["THx2"] + mp.mpf("4.1") ** 2 * k["TH1"]) / mp.mpf("10.9")
        T6 = e ** 2 * mp.mpf("10.9") ** (-2 * e) * ((1 + 1 / cB) * k["Clog"] ** 2 * k["LL2"] + (1 + cB) * 2 ** (2 * e) * Q)
        T7 = 2 * e - g91 * e ** 2 * mp.exp(-2 * mp.euler * e)
        return T1 + T2 + T3 + k4 * T4 + k5 * T5 + k6 * T6 + T7
    return F, Tail0, Bulk0, Bulk1


def scan(F, e0=mp.mpf("0.0227"), n=4000):
    best = (mp.mpf(0), None)
    pts = [mp.mpf(10) ** (-14 + 12 * i / 2000.0) for i in range(2001)] + [e0 * i / n for i in range(1, n + 1)]
    for e in pts:
        if e > e0:
            continue
        v = F(e)
        if v > best[0]:
            best = (v, e)
    return best


if __name__ == "__main__":
    for name, K in (("rza", C), ("hf", HF)):
        F, T0, B0, B1 = make_F(K)
        v, e = scan(F)
        print("%s: Tail0=%s Bulk0=%s Bulk1=%s F(0+)=%s" % (name, mp.nstr(T0, 12), mp.nstr(B0, 12), mp.nstr(B1, 12), mp.nstr(T0 + B0, 12)))
        print("    grid sup F = %s at eps=%s ; F(eps0) = %s ; F(1e-3)=%s F(1e-2)=%s" % (
            mp.nstr(v, 12), mp.nstr(e, 4), mp.nstr(F(mp.mpf("0.0227")), 8), mp.nstr(F(mp.mpf("1e-3")), 8), mp.nstr(F(mp.mpf("1e-2")), 8)))
        h = mp.mpf("1e-7")
        print("    slope dF/deps near 1e-6: %s" % mp.nstr((F(mp.mpf("1e-6") + h) - F(mp.mpf("1e-6"))) / h, 6))
        for lab, kw in (("no G-term (9.1 -> 0)", dict(g91=0)), ("T4 x2", dict(k4=2)), ("T4 x2, T5 x10, T6 x10", dict(k4=2, k5=10, k6=10)),
                        ("Hoelder lambda x3", dict(kl=3)), ("T4 x3", dict(k4=3))):
            Fv = make_F(K, **kw)[0]
            vv, ee = scan(Fv)
            print("    robustness %-24s sup %s at eps=%s" % (lab, mp.nstr(vv, 10), mp.nstr(ee, 4)))
