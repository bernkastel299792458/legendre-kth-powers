"""
cs_bounds.py -- rigorous (Arb) upper bounds for N(sigma,T) from
  (A) Chourasiya--Simonic, arXiv:2507.15184v2, Corollary 1 / Theorem 1 (Ingham-type), and
  (B) Chourasiya--Simonic, eq. (119) / Table 4 (Kadiri--Lumley--Ng-type, improved),
with the corrections found in the audit (REPORT text in the phase1_cs hand-back).

Convention (CS, KLN): N(sigma,T) = #{rho = beta+i gamma : zeta(rho)=0, beta >= sigma,
0 < gamma <= T}, counted with multiplicity.  All bounds are valid for T >= 3e12 only.

Forms
  (A)  N <= B1 T^{3(1-s)/(2-s)} (log T)^{(7-5s)/(2-s)} + B2 log^2 T + B3 log T
  (B)  N <= A T^{8(1-s)/3} (log T)^{6-4s} + B log^2 T

Public API
----------
N_upper_A(sig_lo, sig_hi, T, tier=DEFAULT_TIER) -> arb
N_upper_B(sig_lo, sig_hi, T, tier=DEFAULT_TIER) -> arb
N_upper_JY(sig_lo, sig_hi, T, C1="17.4193", C2="2.231") -> arb   (comparison only)
B_row(sig1, sig2, T0, alpha=None, delta=None, d=None, b4="0.5161") -> (A, B, info)
A_row(sig1, sig2, T0, d=None, kappa=None, delta=None, log10A0=None, b4="0.5161") -> (B1, B2, B3, info)
Each N_upper_* returns an arb whose upper end bounds N(sigma,T) for ALL sigma in
[sig_lo, sig_hi] and ALL T in the ball T: it evaluates at sigma = sig_lo, T = T.upper(),
using every stored row with sigma_lo inside the row and T0 <= T.lower(), and returns the
smallest.  (N is decreasing in sigma and increasing in T; the right-hand sides are
decreasing in sigma and increasing in T for T >= 3e12.)

The b4 option (CS Lemma 7: S_eps(X) = sum_{d,e<=X} mu(d)mu(e)/[d,e]^{1+eps} <= b4)
---------------------------------------------------------------------------------
b4 = "0.5161" (DEFAULT): own Theorem R, work/audit_rza/repair/ (Helfgott-free version):
       S_eps(X) <= 0.5161 for X >= 3e12, 0 < eps <= 0.0227.  NOT YET REVIEWED.
       Lemma 7 uses eps = 2 delta/log X and delta/log X, X = T >= T0, so we require
       2 delta/log T0 <= 0.0227 (checked in Arb).
b4 = "0.5936": RZA arXiv:2603.25961v3 Thm 1.2 rows (0.5936 / 0.5103 / 0.51).  RZA Thm 1.2
       FAILS as proved (work/audit_rza/REPORT.md) -- kept for comparison only.
b4 = arb value: user-supplied; then pass eps_max=..., X0_min=... and take responsibility.

Tiers for the stored rows (N_upper_*):
  "b4_05161" (DEFAULT; alias "corrected"): rows of cs_rows_b4_05161.csv (run_b4_05161.py),
        T0 in {3e12, e^30, e^32, e^35}.  Inputs: refereed + CS (audited preprint) + own
        Theorem R (unreviewed) [+ CS fourth moment, audited, for (A)].
  "rza_05936": earlier corrected rows with b4 = 0.5936 (unproved: RZA fails).
  "paper": printed constants (unproved: b4 = 0.54; (B) also has the log-factor slip).

Self-test:  python -I cs_bounds.py      (exit code 0 = all checks pass)
"""
import csv, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from flint import arb, ctx

ctx.prec = max(ctx.prec, 128)
H_RH = arb(3) * arb(10) ** 12
TOL = arb(10) ** -30   # decimal endpoints are treated as exact up to 1e-30 (binary balls)
DEFAULT_TIER = "b4_05161"
T0_NAMES = {"3e12": H_RH, "e30": arb(30).exp(), "e32": arb(32).exp(), "e35": arb(35).exp()}

# rows: (sig1, sig2, T0name, c1, c2, c3)   (A): c1=B1, c2=B2, c3=B3;   (B): c1=A, c2=B, c3=None
_ROWS_OLD = {
    ("A", "rza_05936"): [("0.93750", "0.96875", "3e12", "38.51", "5.178", "91.82"),
                         ("0.96875", "1.00000", "3e12", "50.58", "4.822", "85.51")],
    ("A", "paper"): [("0.93750", "0.96875", "3e12", "35.35", "5.180", "91.86"),
                     ("0.96875", "1.00000", "3e12", "46.06", "4.897", "86.84")],
    ("B", "rza_05936"): [("0.93750", "0.96875", "3e12", "17.370", "2.750", None),
                         ("0.96875", "0.97500", "3e12", "17.875", "2.474", None),
                         ("0.97500", "0.98125", "3e12", "18.388", "2.420", None),
                         ("0.98125", "0.98750", "3e12", "18.909", "2.366", None),
                         ("0.98750", "0.99375", "3e12", "19.438", "2.312", None),
                         ("0.99375", "1.00000", "3e12", "19.975", "2.258", None)],
    ("B", "paper"): [("0.93750", "0.96875", "3e12", "14.81", "2.558", None),
                     ("0.96875", "0.97500", "3e12", "15.21", "2.301", None),
                     ("0.97500", "0.98125", "3e12", "15.62", "2.249", None),
                     ("0.98125", "0.98750", "3e12", "16.04", "2.204", None),
                     ("0.98750", "0.99375", "3e12", "16.46", "2.153", None),
                     ("0.99375", "1.00000", "3e12", "16.89", "2.101", None)],
}


def _parse_notes(notes):
    out = {}
    for tok in notes.replace(";", " ").split():
        if "=" in tok:
            k, v = tok.split("=", 1)
            out[k] = v
    return out


def _load_csv():
    rows = {("A", "b4_05161"): [], ("B", "b4_05161"): []}
    params = {}
    p = os.path.join(HERE, "cs_rows_b4_05161.csv")
    with open(p, newline="", encoding="utf8") as fh:
        for r in csv.DictReader(fh):
            nt = _parse_notes(r["notes"])
            if r["form"] == "B119":
                key = ("B", "b4_05161")
                row = (r["sigma_lo"], r["sigma_hi"], r["T0"], r["A"], r["B"], None)
                params[(key, row[:3])] = (nt["alpha"], nt["delta"], nt["d"])
            else:
                key = ("A", "b4_05161")
                row = (r["sigma_lo"], r["sigma_hi"], r["T0"], r["A"], r["B"], nt["B3"])
                params[(key, row[:3])] = (nt["d"], nt["kappa"], nt["delta"], nt["log10A0"])
            rows[key].append(row)
    return rows, params


ROWS = dict(_ROWS_OLD)
_csv_rows, PARAMS = _load_csv()
ROWS.update(_csv_rows)


def _tier(t):
    return "b4_05161" if t == "corrected" else t


# ---------------------------------------------------------------------------
def _prep(sig_lo, sig_hi, T):
    sig_lo, sig_hi, T = arb(sig_lo), arb(sig_hi), arb(T)
    if bool(sig_lo > sig_hi):
        raise ValueError("need sig_lo <= sig_hi")
    if not bool(T.lower() >= H_RH):
        raise ValueError("bounds only valid for T >= 3e12 (got %s)" % T.str(5))
    return arb(sig_lo.lower()), arb(T.upper()), arb(T.lower())


def _usable(rows, s, Tlo):
    hits = [r for r in rows if bool(arb(r[0]) - TOL <= s) and bool(s <= arb(r[1]) + TOL)
            and bool(T0_NAMES[r[2]] <= Tlo)]
    if not hits:
        raise ValueError("no stored row contains sigma = %s with T0 <= T" % s.str(6))
    return hits


def rhs_A(B1, B2, B3, s, T):
    L = T.log()
    return B1 * ((3 * (1 - s) / (2 - s)) * L).exp() * ((7 - 5 * s) / (2 - s) * L.log()).exp() \
        + B2 * L ** 2 + B3 * L


def rhs_B(A, B, s, T):
    L = T.log()
    return A * (arb(8) / 3 * (1 - s) * L).exp() * ((6 - 4 * s) * L.log()).exp() + B * L ** 2


def _best(vals):
    return min(vals, key=lambda v: float(v.upper()))


def N_upper_A(sig_lo, sig_hi, T, tier=DEFAULT_TIER):
    s, Th, Tl = _prep(sig_lo, sig_hi, T)
    if bool(s >= 1 - TOL):
        return arb(0)
    rows = _usable(ROWS[("A", _tier(tier))], s, Tl)
    return _best([rhs_A(arb(r[3]), arb(r[4]), arb(r[5]), s, Th) for r in rows])


def N_upper_B(sig_lo, sig_hi, T, tier=DEFAULT_TIER):
    s, Th, Tl = _prep(sig_lo, sig_hi, T)
    if bool(s >= 1 - TOL):
        return arb(0)
    rows = _usable(ROWS[("B", _tier(tier))], s, Tl)
    return _best([rhs_B(arb(r[3]), arb(r[4]), s, Th) for r in rows])


def N_upper_JY(sig_lo, sig_hi, T, C1="17.4193", C2="2.231"):
    """Johnston--Yang (JMAA 527 (2023) Lemma 2.6 / Table 3), sigma in [0.98,1):
    N <= C1 T^{8(1-s)/3} (log T)^{5-2s} + C2 log^2 T.  Default C1 = 17.4193 (JY's printed
    sigma -> 1 entry 17.418 recomputes to 17.41921)."""
    s, Th, Tl = _prep(sig_lo, sig_hi, T)
    if not bool(s >= arb("0.98") - TOL):
        raise ValueError("JY rows used here need sigma >= 0.98")
    L = Th.log()
    return arb(C1) * (arb(8) / 3 * (1 - s) * L).exp() * ((5 - 2 * s) * L.log()).exp() + arb(C2) * L ** 2


def _load_low():
    rows = {}
    p = os.path.join(HERE, "kln_rows_low_sigma.csv")
    if not os.path.exists(p):
        return rows
    with open(p, newline="", encoding="utf8") as fh:
        for r in csv.DictReader(fh):
            if r["sigma_lo"] != r["sigma_hi"]:          # interval rows only
                rows.setdefault(r["form"], []).append((r["sigma_lo"], r["sigma_hi"], r["T0"], r["C1"], r["C2"]))
    return rows


LOW_ROWS = _load_low()


def N_upper_low(sig_lo, sig_hi, T, form="JY52"):
    """Low-sigma rows of kln_rows_low_sigma.csv (run_low_sigma.py), T >= 3e12.
    form 'JY52' (tier refereed):  C1 T^{8(1-s)/3} (log T)^{5-2s} + C2 log^2 T, s in [0.85, 0.98];
    form 'B119' (uses Theorem R b4 = 0.5161): C1 T^{8(1-s)/3} (log T)^{6-4s} + C2 log^2 T,
    s in [0.90, 0.9375]."""
    s, Th, Tl = _prep(sig_lo, sig_hi, T)
    rows = [r + (None,) for r in LOW_ROWS[form]]
    rows = _usable(rows, s, Tl)
    L = Th.log()
    pw = (5 - 2 * s) if form == "JY52" else (6 - 4 * s)
    return _best([arb(r[3]) * (arb(8) / 3 * (1 - s) * L).exp() * (pw * L.log()).exp() + arb(r[4]) * L ** 2
                  for r in rows])


# ---------------------------------------------------------------------------
# b4 option for on-the-fly rows
def b4_value(X0, delta, b4="0.5161", eps_max=None, X0_min=None):
    """Return (b4 ball, note) valid for CS Lemma 7 with all X >= X0 and eps <= 2 delta/log X0.
    Raises ValueError if the chosen lemma does not cover these parameters."""
    X0, delta = arb(X0), arb(delta)
    eps = 2 * delta / X0.log()
    if not bool(delta > 0):
        raise ValueError("delta > 0 needed")
    if isinstance(b4, str) and b4 == "0.5161":
        if not bool(X0 >= H_RH):
            raise ValueError("Theorem R needs X0 >= 3e12")
        if not bool(eps <= arb("0.0227")):
            raise ValueError("Theorem R needs 2 delta/log X0 <= 0.0227 (got %s)" % eps.str(5))
        return arb("0.5161"), "Theorem R (own, unreviewed), X>=3e12, eps<=0.0227"
    if isinstance(b4, str) and b4 == "0.5936":
        if not bool(X0 >= arb(10) ** 12) or not bool(eps <= arb(1) / 25):
            raise ValueError("RZA row needs X0 >= 1e12, eps <= 1/25")
        if bool(X0 < arb(10) ** 16):
            if not bool(2 * delta / (arb(10) ** 16).log() <= arb(1) / 50):
                raise ValueError("delta too large for RZA's 1e16 row")
            return arb("0.5936"), "RZA v3 Thm 1.2 (FAILS as proved)"
        if bool(X0 < arb(10) ** 33):
            if not bool(eps <= arb(1) / 50):
                raise ValueError("eps > 1/50")
            return arb("0.5103"), "RZA v3 Thm 1.2 (FAILS as proved)"
        return arb("0.51"), "RZA v3 Thm 1.2 (FAILS as proved)"
    b = arb(b4)
    if eps_max is None or X0_min is None:
        raise ValueError("custom b4 needs eps_max and X0_min")
    if not (bool(eps <= arb(eps_max)) and bool(X0 >= arb(X0_min))):
        raise ValueError("custom b4: parameters outside the stated range")
    return b, "user-supplied b4 (eps<=%s, X>=%s)" % (eps_max, X0_min)


def B_row(sig1, sig2, T0=H_RH, alpha=None, delta=None, d=None, c8mode="CT19", b4="0.5161", **kw):
    """(B) constants (A, B) valid for sigma in [sig1, sig2] and T >= T0 (T0 >= 3e12)."""
    from cs_kln import KLN
    sig1, sig2, T0 = arb(sig1), arb(sig2), arb(T0)
    if not bool(T0 >= H_RH):
        raise ValueError("T0 >= 3e12 needed")
    alpha = arb("0.0553") + arb("0.4435") * (1 - sig2) if alpha is None else arb(alpha)
    delta = arb("0.3254") if delta is None else arb(delta)
    d = arb("0.3116") if d is None else arb(d)
    b4v, note = b4_value(T0, delta, b4, **kw)
    m = KLN(T0, a1=arb("0.618"), a2=arb("2.8245"), b4=b4v, variant="CS", H=H_RH - 1)
    eta, mu = arb("0.25345"), arb("1.2363")
    a2, b1, chk = m.AB(alpha, d, delta, eta, mu, sig1, sig2, c8mode=c8mode)
    a1, _, chk1 = m.AB(alpha, d, delta, eta, mu, sig1, sig1, c8mode=c8mode)
    chk.update({k + "@sig1": v for k, v in chk1.items()})
    if not all(chk.values()):
        raise ValueError("hypothesis check failed: %s" % chk)
    return a2.max(a1), b1, dict(b4=b4v, b4_note=note, alpha=alpha, delta=delta, d=d, checks=chk)


def A_row(sig1, sig2, T0=H_RH, d=None, kappa=None, delta=None, log10A0=None, K1N=40000,
          b4="0.5161", **kw):
    """(A) constants (B1, B2, B3) valid for sigma in [sig1, sig2] and T >= T0 (Theorem 1 with
    H = H0 = H_RH, h = 1)."""
    import cs_thm1 as c
    sig1, sig2, T0 = arb(sig1), arb(sig2), arb(T0)
    d = arb("0.2946") if d is None else arb(d)
    kappa = arb("0.0739") if kappa is None else arb(kappa)
    delta = arb("0.3032") if delta is None else arb(delta)
    lA = arb("11.45") if log10A0 is None else arb(log10A0)
    b4v, note = b4_value(T0, delta, b4, **kw)
    o = c.thm1_constants(sig1, sig2, d, kappa, delta, c.rpow(arb(10), lA), T0=T0, H0=H_RH,
                         b4=b4v, K1N=K1N)
    if not all(o["hyp"].values()):
        raise ValueError("hypothesis check failed: %s" % o["hyp"])
    return o["B1"], o["B2"], o["B3"], dict(b4=b4v, b4_note=note, out=o)


# ---------------------------------------------------------------------------
def _selftest():
    import cs_thm1 as c
    from cs_kln import KLN
    fails = []

    def ok(cond, msg):
        print(("  OK    " if cond else "  FAIL  ") + msg)
        if not cond:
            fails.append(msg)

    print("1. every stored b4=0.5161 (B) row (cs_rows_b4_05161.csv) bounds its Arb recomputation;"
          " eps = 2delta/logT0 <= 0.0227")
    for r in ROWS[("B", "b4_05161")]:
        al, de, d = PARAMS[(("B", "b4_05161"), r[:3])]
        a, b, info = B_row(r[0], r[1], T0_NAMES[r[2]], al, de, d)
        eps = 2 * arb(de) / T0_NAMES[r[2]].log()
        ok(bool(a <= arb(r[3])) and bool(b <= arb(r[4])) and bool(eps <= arb("0.0227")),
           "(B) T0=%-4s [%s,%s]: A %s<=%s, B %s<=%s, eps=%s" % (r[2], r[0], r[1], a.str(6, radius=False), r[3],
                                                              b.str(5, radius=False), r[4], eps.str(4, radius=False)))
    print("2. every stored b4=0.5161 (A) row bounds its Arb recomputation (K1 by 1e5-step sums)")
    for r in ROWS[("A", "b4_05161")]:
        d, ka, de, lA = PARAMS[(("A", "b4_05161"), r[:3])]
        b1, b2, b3, info = A_row(r[0], r[1], T0_NAMES[r[2]], d, ka, de, lA, K1N=100000)
        ok(bool(b1 <= arb(r[3])) and bool(b2 <= arb(r[4])) and bool(b3 <= arb(r[5])),
           "(A) T0=%-4s [%s,%s]: B1 %s<=%s B2 %s<=%s B3 %s<=%s" % (
               r[2], r[0], r[1], b1.str(6, radius=False), r[3], b2.str(5, radius=False), r[4],
               b3.str(5, radius=False), r[5]))
    print("3. b4 option: guards")
    try:
        b4_value(H_RH, "0.3270")
        ok(False, "delta=0.327 at T0=3e12 must be rejected (eps=0.02276>0.0227)")
    except ValueError:
        ok(True, "delta=0.327 at T0=3e12 rejected (eps > 0.0227)")
    try:
        v, note = b4_value(H_RH, "0.3255")
        ok(abs(float(v.mid()) - 0.5161) < 1e-12, "delta=0.3255 at T0=3e12 accepted (eps=0.022660): b4 = 0.5161")
    except ValueError:
        ok(False, "delta=0.3255 at T0=3e12 should be accepted")
    a0, b0, _ = B_row("0.98", "0.99", H_RH, "0.0598", "0.3253", "0.3119", b4="0.5936")
    a1, b1_, _ = B_row("0.98", "0.99", H_RH, "0.0598", "0.3253", "0.3119")
    ok(bool(a1 < a0), "b4=0.5161 gives smaller A than 0.5936 (%s < %s)" % (a1.str(5, radius=False), a0.str(5, radius=False)))
    print("4. the paper's printed rows are reproduced by the paper's (unproved) inputs")
    p, pr = c.row_params(c.TABLE1[1])
    o = c.thm1_constants(K1N=100000, **p)
    ok(bool(o["B1"] <= pr[0]) and bool(o["B1"] > pr[0] - arb("0.01")),
       "(A) paper row B1 = %s ~ 46.06 with b4=0.54" % o["B1"].str(6, radius=False))
    m = KLN(arb("3e12"), b4=arb("0.54"), variant="CS_literal")
    a, b, _ = m.AB(arb("0.061"), arb("0.336"), arb("0.325"), arb("0.25345"), arb("1.2363"),
                   arb("0.98125"), arb("0.98750"), c8mode="CT19")
    ok(bool(a <= arb("16.04")) and bool(a > arb("16.03")),
       "(B) paper row A = %s ~ 16.04 needs the uncorrected log-factor" % a.str(6, radius=False))
    print("5. sample values, sigma = 0.98 (default tier b4_05161; rows with T0 <= T are used)")
    for LT in ("28.73", "30", "32", "35", "60", "100"):
        T = arb(LT).exp()
        vA = N_upper_A("0.98", "0.99", T)
        vB = N_upper_B("0.98", "0.99", T)
        vJ = N_upper_JY("0.98", "0.99", T)
        print("     logT=%-6s  (A) %-11s (B) %-11s JY %-11s  B/JY=%s" % (
            LT, vA.str(4, radius=False), vB.str(4, radius=False), vJ.str(4, radius=False),
            (vB / vJ).str(3, radius=False)))
        ok(bool(vB < vJ) and bool(vB < vA), "(B) < (A), JY at log T = %s" % LT)
    print("6. monotonicity sanity")
    T1, T2 = arb(30).exp(), arb(31).exp()
    ok(bool(N_upper_B("0.97", "0.97", T1) >= N_upper_B("0.99", "0.99", T1)), "(B) decreasing in sigma")
    ok(bool(N_upper_B("0.98", "0.98", T2) >= N_upper_B("0.98", "0.98", T1)), "(B) increasing in T")
    ok(bool(N_upper_A("0.97", "0.97", T1) >= N_upper_A("0.99", "0.99", T1)), "(A) decreasing in sigma")
    ok(N_upper_A("1", "1", arb("1e13")) == 0, "sigma >= 1 gives 0")
    for tier in ("rza_05936", "paper", "corrected"):
        N_upper_B("0.98", "0.99", T1, tier=tier)
        N_upper_A("0.98", "0.99", T1, tier=tier)
    ok(True, "tiers rza_05936 / paper / corrected(alias) evaluate")
    if LOW_ROWS:
        T = arb(30).exp()
        v1 = N_upper_low("0.95", "0.95", T)
        v2 = N_upper_low("0.93", "0.93", T)
        v3 = N_upper_low("0.93", "0.93", T, form="B119")
        ok(bool(v2 >= v1), "low-sigma JY52 rows: N(0.93) bound %s >= N(0.95) bound %s" % (v2.str(4, radius=False), v1.str(4, radius=False)))
        ok(bool(v3 < v2), "low-sigma B119 (Theorem R) %s < JY52 %s at sigma=0.93, log T=30" % (v3.str(4, radius=False), v2.str(4, radius=False)))
    print("FAILS:", fails)
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(_selftest())
