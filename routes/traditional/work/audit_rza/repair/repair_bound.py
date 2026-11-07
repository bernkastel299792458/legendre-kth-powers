"""
repair_bound.py -- rigorous (Arb) certificate for the repaired b4 lemma (REPORT.md, Theorem R):

    S_eps(X) <= b4   for all X >= X0 and 0 < eps <= eps0,

from the bound (REPORT.md, (R.10))
  S_eps(X) <= F(eps) := (J+0.9999)^{-2eps} Tail0 + X0^{-eps} Bulk0^{1-eps/eps0} Bulk1^{eps/eps0}
            + 2eps X0^{-eps} ax1
            + 2eps 2^eps (4.1 THx + a_eps THxxx) [10.9^{-2eps} ax2/sqrt(10.9) + 47^{-2eps}(1-ax2)/sqrt(47)]
            + 0.03 [ 2eps (mx-mm)/L0 + 2eps mm/log X0 + c1 * u E1(u)/L0 ],  u = 2 eps L0
            + eps^2 10.9^{-2eps} [ (1+1/c) 0.03^2 LL2 + (1+c) 2^{2eps}/10.9 (a_eps^2 THx1 + 8.2 a_eps THx2 + 4.1^2 TH1) ]
            + 2eps,                                          a_eps = (5 + eps 2^eps)/2,
maximised over eps in (0, eps0] by a cell cover with endpoint monotonicity.

Usage: python -I repair_bound.py [X0=3e12] [EPS0=0.0227]
"""
import os, sys, json
HERE = os.path.dirname(os.path.abspath(__file__))
PARENT = os.path.dirname(HERE)
sys.path.insert(0, PARENT)
from rza_common import *
from rza_audited import build

ctx.prec = 128


def load_full_sums():
    ext = json.load(open(os.path.join(PARENT, "out", "thm11_fullsums_ext.json")))
    return ({int(k): arb(v[0], v[1]) for k, v in ext.items()}, {int(k): arb(v[2], v[3]) for k, v in ext.items()})


def load_h(e0s):
    d = json.load(open(os.path.join(HERE, "out", "hweights_%s.json" % e0s)))
    S11 = {int(k): arb(*v) for k, v in d["S11"].items()}
    S12 = {int(k): arb(*v) for k, v in d["S12"].items()}
    return arb(d["W_up"][0]), arb(d["G1h"][0]), arb(d["G2h"][0]), S11, S12


def E1u(u_lo, u_hi):
    """upper bound for sup_{u in [u_lo,u_hi]} u E1(u)  (u E1(u) <= u_hi E1(u_lo); at u_lo=0 use
    E1(u) < log(1+1/u) (Abramowitz-Stegun 5.1.20) and monotonicity of u log(1+1/u))"""
    if u_lo == 0:
        return u_hi * (1 + 1 / u_hi).log()
    return u_hi * u_lo.expint(1)


def variant():
    """'rza': RZA's inputs (Lemma 2.5 with Helfgott/FA-II, threshold 1e12, Lemma 3.1's 0.03).
    'hf'  : Helfgott-free inputs (env RZA_LOG10N etc. set): own sqrt-certificate to N, Ramare 2015,
            Lemma 3.1' log constant C_log = 2^eps0 T_N H1/log 2 (REPORT.md, Lemma R2')."""
    return "hf" if os.environ.get("RZA_LOG10N") else "rza"


def certify(X0s="3e12", e0s="0.0227", J=None, cB=None, ncell=4000, verbose=True, scale=None):
    scale = scale or {}
    X0 = arb(X0s); e0 = arb(e0s)
    var = variant()
    if var == "hf":
        hf = json.load(open(os.path.join(HERE, "out", "hf_inputs_1e%d.json" % LOG10N)))
        assert arb(hf["H2p"]) <= arb(H2_STR), "RZA_H2 must be >= derived H2'"
        inp, o, th, status, Kc = build(False, var_dir=OUTDIR)
        C_log = rpow(2, e0) * arb(hf["T_N"]) * arb(H1_STR) / arb(2).log()
    else:
        inp, o, th, status, Kc = build(False)
        C_log = arb("0.03")
    S11, S12 = load_full_sums()
    Wh, G1h, G2h, S11h, S12h = load_h(e0s)
    H1 = arb(H1_STR)
    L0 = LOGN            # log of the switch threshold N (1e12 for 'rza', 1e10 for 'hf')
    W, G1, G2 = o["APROD"], o["G1"], o["G2"]
    TH1, L1, L2 = o["TH1"], o["L1"], o["L2"]
    THx, THxxx, THx1, THx2 = o["THx"], o["THxxx"], o["THx1"], o["THx2"]
    c1 = o["uc1"]; LL2 = o["loglemma2"]; ax1 = o["ax_1"]
    mx = arb(inp["logmx"]); mm = arb(inp["logmm"])
    assert bool(mm > 0), "mm >= 0 needed for the Lambda bound as written"
    ax2 = arb(19) / 210

    def parts(J):
        Z = arb(J) + arb("0.9999")
        Tail0 = 2 * TH1 / Z + 2 * SQ2 * H1 * L1 / Z.sqrt() + H1 ** 2 * L2
        Bulk0 = W * (arb(2).log() + S11[J]) + (G1 * (1 + SQ2) + G2 * S12[J]) / X0.sqrt()
        Bulk1 = Wh * (arb(2).log() + S11h[J]) + (G1h * (1 + SQ2) + G2h * S12h[J]) / X0.sqrt()
        return Z, Tail0, Bulk0, Bulk1

    if J is None:   # choose J minimising F(0) = Tail0 + Bulk0
        J = min((j for j in S11h if j in S11 and j >= 11), key=lambda j: (parts(j)[1] + parts(j)[2]).upper())
    Z, Tail0, Bulk0, Bulk1 = parts(J)
    assert bool(Bulk1 >= Bulk0), "Hoelder step needs Bulk1 >= Bulk0"
    ratio = Bulk1 / Bulk0
    Q = lambda a: (a * a * THx1 + arb("8.2") * a * THx2 + arb("4.1") ** 2 * TH1) / arb("10.9")
    if cB is None:   # Bohr parameter: minimise (1+1/c) A + (1+c) B at eps0
        Aq = C_log ** 2 * LL2
        Bq = 2 ** (2 * e0) * Q((5 + e0 * 2 ** e0) / 2)
        cB = (Aq / Bq).sqrt()
        cB = arb(cB.mid().str(6, radius=False))
    s109, s47 = arb("10.9").sqrt(), arb(47).sqrt()
    lX0 = X0.log()

    def F(lo, hi):
        """certified upper bound of the right side of (R.10) for all eps in [lo, hi]"""
        two = lambda e: rpow(2, e)
        a_hi = (5 + hi * two(hi)) / 2
        T1 = rpow(Z, -2 * lo) * Tail0
        T2 = rpow(X0, -lo) * Bulk0 * rpow(ratio, hi / e0)
        T3 = 2 * hi * rpow(X0, -lo) * ax1
        T4 = 2 * hi * two(hi) * (arb("4.1") * THx + a_hi * THxxx) * (
            rpow(arb("10.9"), -2 * lo) * ax2 / s109 + rpow(arb(47), -2 * lo) * (1 - ax2) / s47)
        uE = E1u(2 * lo * L0, 2 * hi * L0)
        T5 = C_log * (2 * hi * (mx - mm) / L0 + 2 * hi * mm / lX0 + c1 * uE / L0)
        T6 = hi ** 2 * rpow(arb("10.9"), -2 * lo) * ((1 + 1 / cB) * C_log ** 2 * LL2 + (1 + cB) * two(2 * hi) * Q(a_hi))
        T7 = 2 * hi           # 2/zeta - G(X/10.9)/zeta^2 <= 2/zeta < 2 eps  (G >= 0; review: A10 not needed)
        T4 = T4 * scale.get(4, 1); T5 = T5 * scale.get(5, 1); T6 = T6 * scale.get(6, 1); T3 = T3 * scale.get(3, 1)
        return T1 + T2 + T3 + T4 + T5 + T6 + T7, (T1, T2, T3, T4, T5, T6, T7)

    # cell cover of (0, eps0]: geometric near 0, then uniform
    edges = [arb(0)]
    x = arb("1e-9")
    while bool(x < e0 / ncell):
        edges.append(x); x = x * 2
    for i in range(1, ncell + 1):
        edges.append(e0 * i / ncell)
    worst = None
    rows = []
    for lo, hi in zip(edges[:-1], edges[1:]):
        v, terms = F(lo, hi)
        rows.append((lo, hi, v, terms))
        if worst is None or bool(v.upper() > worst[2].upper()):
            worst = (lo, hi, v, terms)
    b4 = worst[2].upper()
    if verbose:
        print("variant=%s  N=1e%d  H1=%s H2=%s  C_log=%s" % (var, LOG10N, H1_STR, H2_STR, C_log.str(6)))
        print("X0=%s eps0=%s  J=%d  Bohr c=%s" % (X0s, e0s, J, cB.str(6, radius=False)))
        print("  Tail0=%s  Bulk0=%s  Bulk1=%s  ratio^(1/eps0) per unit: lambda=%s" % (
            Tail0.str(10), Bulk0.str(10), Bulk1.str(10), (ratio.log() / e0).str(6)))
        print("  F(0) = Tail0 + Bulk0 = %s   (Theorem 1.1-type bound for S_0, X >= X0)" % (Tail0 + Bulk0).str(10))
        print("  inputs: " + "  ".join("%s=%s" % (k, o[k].upper().str(8, radius=False)) for k in
              ("TH1", "TH2", "TH3", "L1", "L2", "THx", "THxxx", "THx1", "THx2", "uc1", "loglemma2", "ax_1", "G1", "G2", "APROD")))
        print("          mx=%s mm=%s Wh=%s G1h=%s G2h=%s S11(J)=%s S12(J)=%s S11h=%s S12h=%s" % (
            mx.str(8), mm.str(8), Wh.str(10), G1h.str(8), G2h.str(8), S11[J].str(10), S12[J].str(9), S11h[J].str(10), S12h[J].str(9)))
        lo, hi, v, terms = worst
        print("  worst cell [%s, %s]: bound %s  terms %s" % (lo.str(4, radius=False), hi.str(4, radius=False), v.str(10),
                                                          [t.str(4, radius=False) for t in terms]))
        for k in (0, 10, 20, len(rows) // 4, len(rows) // 2, len(rows) - 1):
            lo, hi, v, _t = rows[min(k, len(rows) - 1)]
            print("    cell [%s, %s]  F <= %s" % (lo.str(4, radius=False), hi.str(4, radius=False), v.upper().str(8, radius=False)))
        print("  CERTIFIED: S_eps(X) <= %s for all X >= %s, 0 < eps <= %s   (cells: %d)" % (
            b4.str(10, radius=False), X0s, e0s, len(rows)))
    return dict(F=F, rows=rows, b4=b4, J=J, c=cB, Tail0=Tail0, Bulk0=Bulk0, Bulk1=Bulk1, worst=worst, variant=var,
                consts={k: o[k] for k in ("TH1", "L1", "L2", "THx", "THxxx", "THx1", "THx2", "uc1", "loglemma2",
                                          "ax_1", "G1", "G2", "APROD", "TH2", "TH3")},
                mx=mx, mm=mm, C_log=C_log)


if __name__ == "__main__":
    X0s = sys.argv[1] if len(sys.argv) > 1 else "3e12"
    e0s = sys.argv[2] if len(sys.argv) > 2 else "0.0227"
    r = certify(X0s, e0s)
    print("b4 (rounded up to 4 digits) =", fstr(up(r["b4"])))
