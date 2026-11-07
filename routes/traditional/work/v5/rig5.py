"""v5 Proposition H (sharp truncation, hybrid density): like proof/code/rigorous_hyb.rig_delta, but
  * any density row that contains [u_a, u_b + PAD] may be used (alternatives allowed), and the best one is taken;
  * the zero-free width is a lower bound over ALL heights H_R < |t| <= e^{u_b+PAD}, using the base regions and the
    local Littlewood bands (each piece is decreasing in t, so its minimum is at its right end);
  * optional Chourasiya-Simonic option for [sigma_1, 1 - eta] (if phi5.CFG['CS']).
All hypotheses (H1)-(H4) are checked exactly as in v4."""
from fractions import Fraction as F
from flint import arb
import phi5
from phi5 import CFG, af, eta_base
import rigorous_hyb as RH
from rigorous_hyb import A, certainly_le

PAD = RH.PAD


def eta_upto(Uf):
    """Lower bound for eta(t) over all t with log H_R < log t <= Uf. Heights at or below log t = 28.7296 < log H_R
    carry only zeros on the critical line, so they impose nothing."""
    U = F(Uf)
    start = F(287296, 10000)
    pts = {start, U}
    for lo, hi, _ in CFG['BANDS'] + CFG['CBANDS']:
        for t in (lo, hi):
            if start < t < U:
                pts.add(t)
    pts = sorted(pts)
    best = None
    for p, q in zip(pts[:-1], pts[1:]):
        e = phi5.eta_piece(p, q)
        best = e if best is None or float(e) < float(best) else best
    return best


def rig_delta5(k, a, b, c, sstar, s1=F(49, 50)):
    K = arb(k)
    La, Lb = af(a), af(b)
    L = La.union(Lb)
    th = af(c) / K
    s_star, s_1 = af(sstar), af(s1)
    if not (c > 1 and c / k < F(1, 10)):
        return None, "theta range"
    if a < 1000:
        return None, "x >= e^1000"
    if not (s1 >= F(49, 50) and sstar >= s1 and sstar < 1):
        return None, "sigma params"
    ua, ub = th * La, th * Lb
    u = ua.union(ub)
    if not certainly_le(RH.LOG_HR + RH.LOG2, ua):
        return None, "T >= H_R"
    T_lo, T_hi = ua.exp() / 2, ub.exp() / 2
    if not (certainly_le(arb(51), T_lo) and certainly_le(Lb * Lb, T_lo)):
        return None, "T lower"
    if not certainly_le(4 * T_hi + 2, (La / 10).exp()):
        return None, "T upper"
    Utop = (ub + PAD).upper()
    eta = phi5.eta_running(F(float(Utop)) + F(1, 2 ** 30))
    # Candidate bounds for (trivial part + zero sum); each candidate includes its own trivial term.
    cands = []
    E_triv = u / RH.PI * (-(1 - s_1 - th) * L).exp()
    E_kln = None
    for B1, B3, pw, lc in phi5.klns():
        lamK = L * (1 - 8 * th / 3) - lc * u.log()
        if certainly_le(arb(1), lamK):
            e = (2 * B1 * u ** pw * (L / lamK) * (-(1 - s_star) * lamK).exp() + 2 * B3 * u ** 2 * (-(1 - s_star) * L).exp()).upper()
            E_kln = e if E_kln is None or float(e) < float(E_kln) else E_kln
    good_rows = []
    for T0, T1, s0, C, B, tag, T0f, T1f in phi5.pruned_rows():
        if not (certainly_le(T0, ua) and certainly_le(ub + PAD, T1)):
            continue
        lamB = L * (1 - B * th)
        if not certainly_le(arb(1), lamB):
            continue
        good_rows.append((s0, (2 * C * (L / lamB) * (-eta * lamB).exp()).upper(), (float(T0.mid()), tag)))
    if E_kln is not None:
        for s0, E_bel, rid in good_rows:
            if sstar >= s0:
                cands.append(((E_triv + E_kln + E_bel).upper(), rid))
    if CFG['CS'] and s1 >= CFG['CS_SIGMA']:
        c1, c2, c3 = CFG['CS_CONST']
        lamC = L * (1 - 3 * th)
        if certainly_le(arb(1), lamC):
            pexp = (7 - 5 * s_1) / (2 - s_1)
            val = (E_triv + 2 * c1 * u ** pexp * (L / lamC) * (-eta * lamC).exp() + 2 * (c2 * u ** 2 + c3 * u) * (-eta * L).exp()).upper()
            cands.append((val, ('CS', 'cs')))
    # (G) low-sigma piecewise KLN-type rows (CFG['KROWS']): trivial bound below s1c, KLN-type on [s1c, s*] and a
    #     density row on [s*, 1-eta]; or KLN-type on [s1c, 1-eta].  Needs mu < 1 - s1c for the trivial term to decay.
    if CFG.get('KROWS'):
        for s1c in phi5.S1_LIST:
            if not certainly_le(th, 1 - af(s1c)):
                continue
            Et = u / RH.PI * (-(1 - af(s1c) - th) * L).exp()
            ki = phi5.kpw_integral(u, L, s1c, 1 - eta)
            if ki is not None:
                cands.append(((Et + 2 * ki).upper(), ('KLNpw', str(s1c))))
            if sstar > s1c:
                ks = phi5.kpw_integral(u, L, s1c, sstar)
                if ks is not None:
                    for s0, E_bel, rid in good_rows:
                        if sstar >= s0:
                            cands.append(((Et + 2 * ks + E_bel).upper(), ('KLNpw+row', str(s1c))))
    if not cands:
        return None, "no density option"
    best, brow = min(cands, key=lambda c_: float(c_[0]))
    eps = K * (-L / K).exp()
    E_tr = 2 * RH.M_CHJ / K * ((1 + eps) * (L + eps) ** RH.POW + L ** RH.POW) * (-(th - 1 / K) * L).exp()
    E_pp = (RH.ALPHA1 * (1 + eps).sqrt() - A("0.999")) / K * ((1 / K - arb(1) / 2) * L).exp() \
        + (RH.ALPHA2 * (1 + eps) ** (arb(1) / 3) - A("0.885")) / K * ((1 / K - arb(2) / 3) * L).exp()
    tot = best + E_tr + E_pp
    return float(tot.upper()), dict(row=brow)
