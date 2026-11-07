"""
rza_audited.py -- Theorem 1.2 of RZA v3 recomputed with AUDITED inputs.

Every hard-coded input of the paper is replaced by our independent rigorous value:
  * Euler products / prime sums over p <= 1e8          : out/euler_products.json (rza_euler.py)
      - P0_LX: the TRUE factor (1+f)(1-1/p) (printed factor has a sign error), two-sided tail
      - APROD = W upper bound: 0.428249506... (paper 0.40282372 is wrong)
  * numerical maxima / minima                           : out/scans_*.json (rza_scans.py)
  * Theorem 1.1 bounds Theta(T) for the X-ranges        : recomputed here from the exact full sums
      of rza_thm11_ext.py with the true W, optimising J (upper bounds valid for all X >= T)
  * Bound0 = 0.445 (422 <= X < 1e8, the paper's direct computation) is NOT re-verified.
External inputs kept as in the paper (see REPORT.md, dependency table): E1, E2 (Zuniga-Alterman
2022), H1, H2 and Lemma 2.2 (Helfgott book / RZ25), Lemma 3.1 constants 0.03, 4.1, 5/2 (RZ23
modified), Harm1/Harm2 (Ramare 2016), Dusart, and the m_l(t) pattern constants u1, u2.

Outputs: the nine Theorem 1.2 rows (stated hypotheses), with R re-optimised, in two variants
  (i)  "minimal": the paper's own expressions (incl. its over-generous coefficient K_b);
  (ii) "proof-form K_b": the coefficient as actually derived in the proof of Lemma 6.2;
and b4 for our use in CS Lemma 7 (X >= X0 = 3e12 etc.).
Run:  python -I rza_audited.py
"""
import os, sys, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rza_common import *
from rza_assembly import assemble, PAPER, PRINTED_V3

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "out")


def ball(pair):
    return arb(pair[0], pair[1])


def load_json(name):
    p = os.path.join(OUT, name)
    return json.load(open(p)) if os.path.exists(p) else None


def audited_inputs(var_dir=None):
    """var_dir: folder with the xi_N-dependent outputs (euler_products.json, scans_BC.json,
    scans_EF.json) of a variant threshold N (env RZA_LOG10N); scans A, D, G are N-independent."""
    vd = var_dir or OUT
    E = json.load(open(os.path.join(vd, "euler_products.json")))
    A = load_json("scans_A.json")
    BCD = load_json("scans_BCD.json")
    if var_dir:
        BC = json.load(open(os.path.join(vd, "scans_BC.json")))
        BCD = dict(BCD, B=BC["B"], C=BC["C"])
    EF = json.load(open(os.path.join(vd, "scans_EF.json"))) if var_dir else load_json("scans_EF.json")
    GHI = load_json("scans_GHI.json")
    inp = dict(PAPER)
    inp["H1"], inp["H2"] = H1_STR, H2_STR
    inp["logN"] = LOGN
    status = {}
    # Euler products (finite products to 1e8; the assembly multiplies by the paper's tail factors)
    for k_paper, k_ours in [("P1_M", "P1_M"), ("P1_delta2_M", "P1_delta2_M"), ("P2", "P2"), ("P2_delta", "P2_delta"),
                            ("P3", "P3"), ("P3_spec", "P3_spec"), ("P1x", "P1x"), ("P1x_delta", "P1x_delta"),
                            ("P1_LX", "P1_LX"), ("AP0_LX", "P3"), ("AP1_LX", "P3_spec"), ("PPdelta", "PPdelta_all"),
                            ("Sumx_p3", "Sumx_p3"), ("ASumx_p3", "ASumx_p3")]:
        inp[k_paper] = ball(E[k_ours])
    inp["P0_LX"] = ball(E["P0_LX_true"])
    inp["P0_two_sided_tail"] = True
    inp["APROD"] = ball(E["APROD_all"])
    status["euler"] = "Arb p<=1e8 (rza_euler.py)"
    # scans
    if A:
        a = {d["name"]: d for d in A["A"]}
        inp["Fmx1"], inp["Fmx2"], inp["mx1"] = a["sigma1"]["sup_upper"], a["sigma2"]["sup_upper"], a["Sigma1"]["sup_upper"]
        inp["T_aux1"] = str(a["sigma1"]["N"])
        status["A"] = "scan to %s" % a["sigma1"]["N"]
    else:
        status["A"] = "PAPER VALUES (scan A not available)"
    if BCD:
        inp["mx2"] = BCD["B"][0]["sup_upper"]
        inp["mx3"] = BCD["C"][0]["sup_upper"]
        d = {x["name"]: x for x in BCD["D"]}
        inp["mxxx_aux11"], inp["mx_aux11"] = d["Xi1"]["sup_upper"], d["Xi2"]["sup_upper"]
    if EF:
        e = EF["E"]["true"]
        f = EF["F"]["true"]
        inp["logmx_num"] = arb(e["sup_K_minus_clog"]).upper()
        inp["logmm_num"] = arb(e["inf_K_minus_clog_np1"]).lower()
        inp["log2mx_num"] = arb(f["sup_K_minus_clog"]).upper()
        inp["log2mm_num"] = arb(f["inf_K_minus_clog_np1"]).lower()
        status["EF"] = "scan to 2e8"
    else:
        status["EF"] = "PAPER VALUES (scan E,F not available)"
    if GHI:
        g = GHI["G"]["G_1e8_1p1"]
        assert g * (1 - 1e-8) > 9.1
    inp["v3_with_tails"] = True
    return inp, status


def analytic_K_consts(o, inp):
    """constant terms of K_1, K_2 for X >= 2e8 (proofs of Lemmas 4.11, 4.13), with the TRUE c"""
    Mv = arb(M)
    xi = XI
    N = arb(2) * arb(10) ** 8
    E1, E2 = arb(inp["E1"]), arb(inp["E2"])
    f2 = o["f2_lx"]
    W2_lx = (SQ2 - 1) / (SQ2 - 1 + abs(2 * f2 - 1)) * (E1 + E2 * abs(2 * f2 - 1) / (SQ2 - 1))
    F2P1 = 1 + abs(2 * f2 - 1) / (SQ2 - 1)
    P1full = F2P1 * arb(inp["P1_LX"]) * ((1 - rpow(Mv, -xi)) ** -1 * (1 - rpow(Mv, -arb(1) / 2)) ** -1 * B_kappa(arb(1) / 2 + xi)).exp()
    Ttail = (1 + 2 * rpow(Mv, xi - 2)) * C_kappa(1 + xi) / ((1 - rpow(Mv, -xi) - Mv ** -2) * (1 - 1 / Mv))
    Sumx = EG + arb(2).log() / (f2 + 1) + arb(inp["Sumx_p3"])
    Sumx_hi, Sumx_lo = Sumx + Ttail, Sumx - Ttail          # two-sided (paper assumed one-sided)
    err1 = W2_lx * P1full / N.sqrt()
    K1_hi = o["uc1"] * Sumx_hi + err1
    K1_lo = o["lc1"] * Sumx_lo - err1
    Af2 = o["Af2"]
    AF2P1 = 1 + abs(2 * Af2 - 1) / (SQ2 - 1)
    AP1full = AF2P1 * arb(inp["AP1_LX"]) * (2 * (1 - rpow(Mv, -xi)) ** -2 * (1 - rpow(Mv, -arb(1) / 2)) ** -1 * B_kappa(arb(1) / 2 + xi)).exp()
    ASumx = arb(2).log() / (Af2 + 1) + arb(inp["ASumx_p3"]) + EG
    Atail = 2 * (1 + rpow(Mv, xi - 2)) / (1 - 2 * rpow(Mv, -xi) - Mv ** -2) / (1 - 1 / Mv) * C_kappa(1 + xi)
    err2 = W2_lx * AP1full / N.sqrt()      # paper reuses w_1 of K_1 (valid: larger than K_2's w)
    K2_hi = o["uc2"] * ASumx + err2
    K2_lo = o["lc2"] * (ASumx - Atail) - err2
    return K1_lo, K1_hi, K2_lo, K2_hi


def theta_full(o, S11, S12, X0, J):
    """Theorem 1.1 bound (Part 2) valid for ALL X >= X0, with all n | Pi(j) (no cutoff)."""
    Z = arb(J) + arb("0.9999")
    H1 = arb(H1_STR)
    return (2 * o["TH1"] / Z + 2 * SQ2 * H1 * o["L1"] / Z.sqrt() + H1 ** 2 * o["L2"]
            + o["APROD"] * (arb(2).log() + S11[J]) + (o["G1"] * (1 + SQ2) + o["G2"] * S12[J]) / arb(X0).sqrt())


def best_theta(o, S11, S12, X0):
    best = None
    for J in S11:
        if J < 2:
            continue
        v = theta_full(o, S11, S12, X0, J)
        if best is None or v.upper() < best[1].upper():
            best = (J, v)
    return best


def best_R(o, T, T0, S, lo=None, hi=4000):
    lo = lo or S + 1
    best = None
    for R in range(lo, hi):
        v = o["Omega1"](R, T, T0).max(o["Omega2"](R, S, T, T0))
        if best is None or v.upper() < best[1].upper():
            best = (R, v)
    return best


def build(variant_kb=False, var_dir=None):
    inp, status = audited_inputs(var_dir)
    inp["Kb_proof_form"] = variant_kb
    o = assemble(inp)                                # first pass: auxiliary constants
    # K_1 / K_2 constants: max(numerical scan, analytic X >= 2e8)
    K1_lo, K1_hi, K2_lo, K2_hi = analytic_K_consts(o, inp)
    if "logmx_num" in inp:
        inp["logmx"] = arb(inp["logmx_num"]).max(K1_hi.upper())
        inp["logmm"] = arb(inp["logmm_num"]).min(K1_lo.lower())
        inp["log2mx"] = arb(inp["log2mx_num"]).max(K2_hi.upper())
        inp["log2mm"] = arb(inp["log2mm_num"]).min(K2_lo.lower())
    # Theorem 1.1 bounds with true W
    ext = json.load(open(os.path.join(OUT, "thm11_fullsums_ext.json")))
    S11 = {int(k): arb(v[0], v[1]) for k, v in ext.items()}
    S12 = {int(k): arb(v[2], v[3]) for k, v in ext.items()}
    o = assemble(inp)
    th = {}
    for key, X0 in [(("1e8", "1e12"), "1e8"), (("1e12", "1e16"), "1e12"), (("1e16", "1e33"), "1e16"),
                    (("1e33", "1e50"), "1e33"), (("3e12", "1e16"), "3e12"), (("3e12", "1e50"), "3e12")]:
        J, v = best_theta(o, S11, S12, X0)
        th[key] = (J, v)
    inp["THETA"] = {k: v[1] for k, v in th.items()}
    o = assemble(inp)
    return inp, o, th, status, (K1_lo, K1_hi, K2_lo, K2_hi)


if __name__ == "__main__":
    for variant in (False, True):
        inp, o, th, status, Kc = build(variant)
        print("=" * 100)
        print("VARIANT:", "proof-form K_b (Lemma 6.2 as derived)" if variant else "minimal (paper's own expressions)")
        print("input status:", status)
        if not variant:
            print("audited auxiliary constants:")
            for k in ["THx1", "THx2", "TH1", "TH2", "L1", "TH3", "L2", "THxxx", "THx", "lc1", "uc1", "loglemma1_2",
                      "lc2", "uc2", "loglemma2", "G1", "G2", "APROD", "K_a", "K_b", "K_c", "D0", "D1", "D2", "D3"]:
                print("  %-12s %s" % (k, show(o[k], 12)))
            print("  logmx=%s logmm=%s log2mx=%s log2mm=%s" % tuple(show(arb(inp[k]), 10) for k in ("logmx", "logmm", "log2mx", "log2mm")))
            print("  analytic K consts (X>=2e8): K1 in [%s, %s], K2 in [%s, %s]" % tuple(show(x, 8) for x in Kc))
            print("Theorem 1.1 bounds (true W, optimised J, valid for all X >= T):")
            for k, (J, v) in th.items():
                print("  Theta[%s,%s) J=%d  %s   (rounded up %s)" % (k[0], k[1], J, show(v, 10), fstr(up(v))))
        print("Theorem 1.2 rows: printed v3 | paper's R replay with audited inputs | re-optimised R")
        rows = [("422", "1e8", 158, 100), ("1e8", "1e12", 347, 100), ("1e12", "1e16", 112, 25), ("1e12", "1e16", 204, 50),
                ("1e16", "1e33", 243, 50), ("1e16", "1e33", 461, 100), ("1e33", "1e50", 242, 25), ("1e33", "1e50", 440, 50),
                ("1e33", "1e50", 836, 100)]
        for (T, T0, R, S), pv in zip(rows, PRINTED_V3):
            same = o["Omega1"](R, T, T0).max(o["Omega2"](R, S, T, T0))
            Rb, vb = best_R(o, T, T0, S)
            print("  [%s,%s) eps<=1/%d  printed %-7s  R=%d: %s   best R=%d: %s -> %s%s" % (
                T, T0, S, pv, R, show(same, 7), Rb, show(vb, 8), fstr(up(vb)),
                "   (uses unverified Bound0=0.445)" if T == "422" else ""))
        print("b4 for our use (CS Lemma 7, X = hT >= X0):")
        for (T, T0, S) in [("3e12", "1e16", 25), ("3e12", "1e16", 44), ("1e16", "1e33", 50), ("1e16", "1e33", 56),
                           ("1e33", "1e50", 25), ("1e33", "1e50", 116)]:
            Rb, vb = best_R(o, T, T0, S)
            print("  X in [%s,%s), eps <= 1/%d: R=%d  %s -> %s" % (T, T0, S, Rb, show(vb, 8), fstr(up(vb))))
