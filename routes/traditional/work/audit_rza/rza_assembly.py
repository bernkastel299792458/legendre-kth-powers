"""
rza_assembly.py -- Arb replay of the Sage computation behind Theorems 1.1 (X >= 1e33 row) and
1.2 of Ramare--Zuniga Alterman, arXiv:2603.25961v3.

The structure is a line-by-line transcription of the Sage block of the v3 source
(OnADoubleMobiusSum-20.tex lines 82-546).  All hard-coded numerical inputs are collected in
PAPER (verbatim from the source).  `assemble(inp)` takes such a dict (possibly with audited
replacements, see rza_inputs_audited.py) and returns every intermediate constant and the nine
Theorem 1.2 values.

Run:  python -I rza_assembly.py          (prints the paper replay + sensitivity table)
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rza_common import *

F = lambda s: arb(s)

# ---- hard-coded inputs of the paper (v3 Sage block), as exact decimals --------------------
PAPER = dict(
    E1="1.044", E2="0.232", H1="0.010032", H2="0.0296",
    Harm1="1.040", Harm2="1.048",
    P1_M="2.90950563", P1_delta2_M="306.1036494",
    Fmx1="6.2359917454422", Fmx2="3.16843122347233", mx1="2.06803754617859",
    P2="1.638009774", P2_delta="13.81614454", mx2="1.90380793763037",
    P3="1.031648197", P3_spec="3.191814808", mx3="2.67710025",
    P1x="1.2159031", P1x_delta="7.26497961",
    mxxx_aux11="2.2526506709", mx_aux11="1.587160669",
    P0_LX="0.694045937", P1_LX="1.079535589", Sumx_p3="0.656118309",
    logmx="1.29424331261228", logmm="0.505508801388535",
    AP0_LX="1.031648197", AP1_LX="3.191814808", ASumx_p3="0.3611216153",
    log2mx="1.29424331261228", log2mm="0.505508801388535",
    APROD="0.40282372", ASUM_p="2.046752376", PPdelta="4.94778677",
    S11_80="0.333415398793", S12_80="41346.25411",
    Bound0="0.445", Bound1="0.65924939690269", Bound2="0.4987002674334",
    Bound3="0.4669804238966",
    u1="2323/30030", u2="57731/570570", subs="0.8988", c="0.001", value1="9.1",
    # thresholds used in the paper
    T_aux1="4e9", T_aux2="1e7", T_aux3="1e6", T_xi="5e6",
    # flags reproducing paper choices (False = paper behaviour)
    v3_with_tails=False,
)


def _ar(s):
    if isinstance(s, arb):
        return s
    s = str(s)
    if "/" in s:
        a, b = s.split("/")
        return arb(a) / arb(b)
    return arb(s)


def amax(a, b):
    return a.max(b)


def assemble(inp=PAPER, rows=None):
    I = {k: (_ar(v) if isinstance(v, (str, int, float, arb)) and not isinstance(v, bool) else v)
         for k, v in inp.items()}
    Mv = arb(M)
    E1, E2, H1, H2 = I["E1"], I["E2"], I["H1"], I["H2"]
    xi = XI
    g0_2 = arb(3).sqrt() * (SQ2 - 1) / 2
    g2_2 = H2 / H1 * (1 - 1 / rpow(2, xi))
    d2 = arb(5) / 12
    d1 = arb(1) / 3
    o = {}

    def F2(f):         # 1 - (1-f)/2 - f/4         (H_{f'}(0) factor at p=2, alpha=0)
        return 1 - (1 - f) / 2 - f / 4

    def F2d(f, d):     # 1 + |1-f|/2^{1-d} + |f|/2^{2-2d}
        return 1 + abs(1 - f) / rpow(2, 1 - d) + abs(f) / rpow(2, 2 - 2 * d)

    # Lemma 4.5 (Aux1)
    fx1 = 1 / (SQ2 - 1) ** 2
    fx2 = g0_2 / (SQ2 - 1) ** 2
    f1 = g0_2 ** 2 / (SQ2 - 1) ** 2
    Cm = (2 + rpow(Mv, d2 - arb(1) / 2) + rpow(Mv, d2 - 1)) / (1 - rpow(Mv, -arb(1) / 2))
    tail_main = (2 / (1 - rpow(Mv, -arb(1) / 2)) * B_kappa(arb(3) / 2)).exp()
    tail_d2 = (Cm * B_kappa(arb(3) / 2 - d2)).exp()
    Tx = I["T_aux1"]
    errc = (2 - d2) / (1 - d2) * A_delta(d2)

    def vsig(f):
        return F2(f) * I["P1_M"] * tail_main + errc * F2d(f, d2) * I["P1_delta2_M"] * tail_d2 * rpow(Tx, -d2)
    o["vx1"], o["vx2"], o["v1"] = vsig(fx1), vsig(fx2), vsig(f1)
    o["THx1"] = amax(o["vx1"], I["Fmx1"])
    o["THx2"] = amax(o["vx2"], I["Fmx2"])
    o["TH1"] = amax(o["v1"], I["mx1"])

    # Lemma 4.6 (Aux2)
    f2_2 = g0_2 * g2_2 * (1 + (rpow(2, xi - arb(1) / 2) + 1) / (rpow(2, xi) - 1))
    cm0_2 = (1 + rpow(Mv, arb(1) / 2 - xi)) / (1 - rpow(Mv, -xi))
    cmd_2 = (1 + rpow(Mv, -arb(1) / 6) + rpow(Mv, arb(1) / 2 - xi) + rpow(Mv, -arb(2) / 3)) / (1 - rpow(Mv, -xi))
    o["v2"] = F2(f2_2) * I["P2"] * (cm0_2 * B_kappa(arb(3) / 2)).exp() + \
        arb(5) / 2 * A_delta(d1) * F2d(f2_2, d1) * I["P2_delta"] * (cmd_2 * B_kappa(arb(7) / 6)).exp() * rpow(I["T_aux2"], -d1)
    o["TH2"] = amax(o["v2"], I["mx2"])
    L0 = _ar(inp["logN"]) if "logN" in inp else LOGN   # log of the switch threshold N (paper 10^12)
    o["L1"] = 2 * o["TH2"] / L0                                  # Cor 4.7

    # Lemma 4.8 (Aux3)
    f3_2 = g2_2 ** 2 * rpow(2, 2 * xi - 1) / (rpow(2, xi) - 1) ** 2
    F3_2 = F2(f3_2)
    F3_2_spec = 1 + abs(f3_2 - 1) / (SQ2 - 1)
    W = (SQ2 - 1) / (SQ2 - 1 + abs(f3_2 - 1)) * (E1 + abs(f3_2 - 1) * E2 / (SQ2 - 1))
    if I["v3_with_tails"]:
        cm0_3 = (2 + rpow(Mv, xi - 2)) / (1 - rpow(Mv, -xi)) ** 2
        cmd_3 = 2 / (1 - rpow(Mv, -xi)) ** 2 / (1 - rpow(Mv, -arb(1) / 2))
        o["v3"] = F3_2 * I["P3"] * (cm0_3 * B_kappa(1 + xi)).exp() + \
            3 * W * F3_2_spec * I["P3_spec"] * (cmd_3 * B_kappa(arb(1) / 2 + xi)).exp() * rpow(I["T_aux3"], -arb(1) / 2)
    else:   # paper code: no tail factors, and F3_2_spec omitted (harmless: v3 < mx3)
        o["v3"] = F3_2 * I["P3"] + 3 * W * I["P3_spec"] * rpow(I["T_aux3"], -arb(1) / 2)
    o["TH3"] = amax(o["v3"], I["mx3"])
    o["L2"] = o["TH3"] * (1 / L0 - 1 / L0 ** 2) + o["TH3"] / L0 ** 2   # Cor 4.9

    # Lemma 4.10 (auxnu2)
    fxxx = (SQ2 + 1) / 2
    fx = g0_2 * (SQ2 + 1) / 2
    def F2h(f):
        return 1 - (1 - f * SQ2) / 2 - f * SQ2 / 4
    def F2hd(f):
        return 1 + abs(1 - f * SQ2) / rpow(2, 1 - d1) + abs(f * SQ2) / rpow(2, 2 - 2 * d1)
    tB = B_kappa(arb(3) / 2).exp()
    tBd = ((1 + rpow(Mv, -arb(1) / 6) + rpow(Mv, -arb(2) / 3)) * B_kappa(arb(7) / 6)).exp()
    def vxi(f):
        return 2 * F2h(f) * I["P1x"] * tB + 4 * A_delta(d1) * F2hd(f) * I["P1x_delta"] * tBd / rpow(I["T_xi"], d1)
    o["vxxx"], o["vx"] = vxi(fxxx), vxi(fx)
    o["THxxx"] = amax(o["vxxx"], I["mxxx_aux11"])
    o["THx"] = amax(o["vx"], I["mx_aux11"])

    # Lemma 4.11 / Cor 4.12 (K1, L1(X))
    f2_lx = g2_2 / 4 * rpow(2, xi) / (rpow(2, xi) - 1)
    W2_lx = (SQ2 - 1) / (SQ2 - 1 + abs(2 * f2_lx - 1)) * (E1 + E2 * abs(2 * f2_lx - 1) / (SQ2 - 1))
    F2_LX = 1 - (1 - 2 * f2_lx) / 2 - f2_lx / 2
    o["f2_lx"] = f2_lx
    o["lc1"] = F2_LX * I["P0_LX"]
    o["uc1"] = F2_LX * I["P0_LX"] * ((1 - rpow(Mv, -xi)) ** -1 * B_kappa(1 + xi)).exp()
    if inp.get("P0_two_sided_tail", False):   # true factor (1+f)(1-1/p) has two-signed tail
        tau = (B_kappa(1 + xi) + 2 * B_kappa(2) + B_kappa(3)) / (1 - rpow(Mv, -xi)) * arb("1.0001")
        o["lc1"] = F2_LX * I["P0_LX"] * (-tau).exp()
        o["uc1"] = F2_LX * I["P0_LX"] * tau.exp()
    o["loglemma1_1"] = o["uc1"]
    # Cor 4.12: L1 <= c1 log(logX/L0) + (logmx - min(logmm,0))/L0  (paper drops logmm, valid iff logmm >= 0)
    o["loglemma1_2"] = (I["logmx"] - I["logmm"].min(arb(0))) / L0

    # Lemma 4.13 / Cor 4.14 (K2, L2(X))
    Af2 = g2_2 ** 2 / 4 * rpow(2, 2 * xi) / (rpow(2, xi) - 1) ** 2
    AF2_LX = 1 - (1 - 2 * Af2) / 2 - Af2 / 2
    o["Af2"] = Af2
    o["lc2"] = AF2_LX * I["AP0_LX"]
    o["uc2"] = AF2_LX * I["AP0_LX"] * ((2 + rpow(Mv, xi - 2)) * (1 - rpow(Mv, -xi)) ** -2 * B_kappa(1 + xi)).exp()
    # Cor 4.14: L2 <= c2/L0 + (log2mx - min(log2mm,0))/L0^2 (paper drops log2mm, valid iff log2mm >= 0)
    o["loglemma2"] = o["uc2"] / L0 + (I["log2mx"] - I["log2mm"].min(arb(0))) / L0 ** 2

    # Lemma 5.2 (G_q)
    f2 = arb(1) / 4
    W2 = (SQ2 - 1) / (SQ2 - 1 + abs(2 * f2 - 1)) * (E1 + E2 * abs(2 * f2 - 1) / (SQ2 - 1))
    APROD_delta = I["PPdelta"] * (B_kappa(arb(3) / 2) / (1 - rpow(Mv, -arb(1) / 2))).exp()
    o["G1"] = W2 * APROD_delta
    o["G2"] = E2 * APROD_delta
    o["APROD"] = I["APROD"]

    # Theorem 1.1, X >= 1e33
    Z80 = arb("80.9999")
    o["Thresh33_1"] = 2 * o["TH1"] / Z80 + 2 * SQ2 * H1 * o["L1"] / Z80.sqrt() + H1 ** 2 * o["L2"]
    o["Thresh33_2"] = I["APROD"] * (I["S11_80"] + arb(2).log()) + (o["G2"] * I["S12_80"] + o["G1"] * (1 + SQ2)) / arb(10) ** (arb(33) / 2)
    o["Bound4"] = o["Thresh33_1"] + o["Thresh33_2"]

    # Lemma 6.2 / 6.3 constants
    o["ax_1"] = (6 / PI ** 2 * (arb("10.9") / 5).log() + I["Harm2"] - I["Harm1"]) / 30
    o["ax_2"] = amax(I["u1"], I["u2"])
    subs, c, value1 = I["subs"], I["c"], I["value1"]

    Theta = {("422", "1e8"): I["Bound0"], ("1e8", "1e12"): I["Bound1"], ("1e12", "1e16"): I["Bound2"],
             ("1e16", "1e33"): I["Bound3"], ("1e33", "1e50"): o["Bound4"]}
    if "THETA" in inp:
        Theta.update({k: _ar(v) for k, v in inp["THETA"].items()})
    o["Theta"] = Theta
    THx, THxxx, THx1, THx2, TH1 = o["THx"], o["THxxx"], o["THx1"], o["THx2"], o["TH1"]
    ll11, ll12, ll2, ax_1, ax_2 = o["loglemma1_1"], o["loglemma1_2"], o["loglemma2"], o["ax_1"], o["ax_2"]
    s109 = arb("10.9").sqrt()
    s47 = arb(47).sqrt()
    K_b = ax_2 * THx * arb("4.1") / s109 + THxxx * arb("2.5") / s109 + subs * THx * arb("4.1") / s47 + THxxx * arb("2.5") / s47
    if inp.get("Kb_proof_form", False):   # coefficient as derived in the proof of Lemma 6.2 (smaller)
        K_b = ax_2 * (THx * arb("4.1") + THxxx * arb("2.5")) / s109 + subs * (THx * arb("4.1") + THxxx * arb("2.5")) / s47
    K_c = ax_2 * THxxx / 2 / s109 + subs * THxxx / 2 / s47
    D0 = (1 + 1 / c) * arb("0.03") ** 2 * ll2
    D1 = (arb(25) / 4 * THx1 + 5 * arb("4.1") * THx2 + arb("4.1") ** 2 * TH1) * (c + 1) / arb("10.9")
    D2 = (arb(10) / 4 * THx1 + arb("4.1") * THx2) * (c + 1) / arb("10.9")
    D3 = THx1 * (c + 1) / 4 / arb("10.9")
    K_a = arb("0.03") * ll12 + ax_1
    o.update(K_b=K_b, K_c=K_c, D0=D0, D1=D1, D2=D2, D3=D3, K_a=K_a)
    KL = arb("0.03") * ll11 / (1 + L0)

    def ind1(T0): return 1 if bool(arb(T0) > arb(10) ** 12) else 0
    def ind2(T): return 1 if bool(arb(T) >= arb("10.9") * arb(10) ** 8) else 0

    def Grr(ee, T):
        return 2 * ee - ind2(T) * value1 * ee ** 2 / (2 * ee * EG).exp()

    def Omega1(R, T, T0):
        R = arb(R); Tl = arb(T).log()
        e = 1 / R
        mn1 = e.min(1 / Tl); mn2 = (2 * e).min(1 / Tl)
        th = Theta[(T, T0)]
        p1 = th + KL * ind1(T0) + Grr(e, T)
        p2 = mn2 * (arb("0.03") * ll11 * ind1(T0) + K_b * rpow(2, e) + K_c * rpow(2, 2 * e) / R)
        p3 = mn1 * 2 * K_a
        p4 = mn2 / (2 * R) * (D0 + D1 * rpow(2, 2 * e) + D2 * rpow(2, 3 * e) / R + D3 * rpow(2, 4 * e) / R ** 2)
        return p1 + p2 + p3 + p4

    def Omega2(R, S, T, T0):
        R = arb(R); S = arb(S); Tl = arb(T).log()
        e = 1 / S
        x1 = (-Tl / R).exp(); x2 = (-2 * Tl / R).exp()
        th = Theta[(T, T0)]
        q1 = x2 * th + KL * ind1(T0) + Grr(e, T)
        q2 = e * x1 * 2 * K_a
        q3 = 2 * e * x2 * (arb("0.03") * ll11 * ind1(T0) + K_b * rpow(2, e) + K_c * rpow(2, 2 * e) / S)
        q4 = e ** 2 * x2 * (D0 + D1 * rpow(2, 2 * e) + D2 * rpow(2, 3 * e) / S + D3 * rpow(2, 4 * e) / S ** 2)
        return q1 + q2 + q3 + q4

    o["Omega1"], o["Omega2"] = Omega1, Omega2
    ROWS = [("422", "1e8", 158, 100), ("1e8", "1e12", 347, 100),
            ("1e12", "1e16", 112, 25), ("1e12", "1e16", 204, 50),
            ("1e16", "1e33", 243, 50), ("1e16", "1e33", 461, 100),
            ("1e33", "1e50", 242, 25), ("1e33", "1e50", 440, 50), ("1e33", "1e50", 836, 100)]
    res = []
    for (T, T0, R, S) in (rows or ROWS):
        w1, w2 = Omega1(R, T, T0), Omega2(R, S, T, T0)
        res.append(dict(T=T, T0=T0, R=R, S=S, O1=w1, O2=w2, val=max(up(w1), up(w2)), raw=w1.max(w2)))
    o["rows"] = res
    return o


def best_R(o, T, T0, S, Rmax=3000):
    """Optimise R (integer) as the paper does: minimise max(Omega1, Omega2)."""
    best = None
    for R in range(S + 1, Rmax):
        v = o["Omega1"](R, T, T0).max(o["Omega2"](R, S, T, T0))
        if best is None or v.upper() < best[1].upper():
            best = (R, v)
        elif R > best[0] + 400:
            break
    return best


PRINTED_V3 = ["0.5107", "0.689", "0.5936", "0.5501", "0.5103", "0.4901", "0.51", "0.4905", "0.4794"]

if __name__ == "__main__":
    o = assemble(PAPER)
    print("Replay of the v3 Sage computation with the paper's own hard-coded inputs")
    for k in ["THx1", "THx2", "TH1", "TH2", "L1", "TH3", "L2", "THxxx", "THx", "lc1", "uc1",
              "loglemma1_2", "lc2", "uc2", "loglemma2", "G1", "G2", "Bound4", "ax_1", "ax_2",
              "K_a", "K_b", "K_c", "D0", "D1", "D2", "D3"]:
        print("  %-12s %s" % (k, show(o[k], 14)))
    print("Theorem 1.2 rows (T, T0, R, S): Omega1, Omega2 -> stated value; printed v3")
    ok = True
    for r, pv in zip(o["rows"], PRINTED_V3):
        same = fstr(r["val"]) == pv or float(fstr(r["val"])) == float(pv)
        ok &= same
        print("  [%s,%s) R=%d S=%d  O1=%s  O2=%s  -> %s   printed %s  %s" % (
            r["T"], r["T0"], r["R"], r["S"], show(r["O1"], 10), show(r["O2"], 10), fstr(r["val"]), pv,
            "OK" if same else "MISMATCH"))
    print("ALL ROWS REPRODUCED" if ok else "SOME ROWS DIFFER")
