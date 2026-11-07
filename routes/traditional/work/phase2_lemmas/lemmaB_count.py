"""
Lemma B (rigorous, Arb): zeros of zeta in a box near the 1-line.

Box  B(t0; delta, h) = {beta + i gamma : 1 - delta <= beta <= 1, |gamma - t0| <= h/2},
with 3e12 <= t0 - h/2,  t0 + h/2 <= T,  and every zero in B has beta <= 1 - nu  (zero-free region).
Bellotti's boxes (4.1) have h = delta.

Statement.  Let 0 < r < 1/2 with sqrt((r+delta)^2 + h^2/4) < 1/2, let
P(theta) = a0 + cos(theta) + sum_{k=2}^K a_k cos(k theta) >= 0 for all theta, a_k >= 0. Then
  #B <= [ a0 * Z(r) + sum_k a_k (BTZ(r, log(kT)) + 1e-24) + BTZ(r, log T) + 1e-24 ] / (c_min - 4(r+delta)/(1+2r)^2)
where Z(r) = -zeta'/zeta(1+r),
  BTZ(r, l) = (l + 4.709774)/(4+8r) + (4/pi - 1) log(1 + 1/r)/(1+2r) + 2.6908,
  c_min = min_{X in [r+nu, r+delta]} X/(X^2 + h^2/4),
provided the denominator is positive.

Inputs: Heath-Brown (1992) Lemma 3.2 (refereed); the bound -J <= BTZ(r, log T) proved inside the
proof of Thorner-Zaman, Forum Math. 36 (2024), Prop. 2.11 (refereed); Hiary, Indag. Math. 27 (2016), 0.63 t^{1/6} log t
(refereed) via TZ Prop. 2.10 [citation corrected after review; HPY 2024's 0.618 also suffices].  Everything numerical here is Arb.

Main output: cf_upper(...) = rigorous upper bound of sup_{delta in [nu(T), 1-alpha0]} #B/(delta log T)
uniformly for log T in [L0, L1]; this replaces Bellotti's  b1 + b2/(nu(T0) log T0).
"""
import math
from fractions import Fraction as Fr
from flint import arb, arb_series, ctx
import numpy as np

ctx.prec = 100
PI = arb.pi()


def f_up(x):
    return math.nextafter(float(x.upper()), math.inf)


def f_down(x):
    return math.nextafter(float(x.lower()), -math.inf)


# ---------------------------------------------------------------- zero-free regions (as nu(L), L=log T)
def nu_classical(L, Z1="5.558691"):
    return 1 / (arb(Z1) * L)


def nu_ford(L):
    """Bellotti (2.2): (0.04962 - 0.0196/(J+1.15)) / (J + 0.685 + 0.155 log L), J = L/6 + log L + log 0.618."""
    J = L / 6 + L.log() + arb("0.618").log()
    return (arb("0.04962") - arb("0.0196") / (J + arb("1.15"))) / (J + arb("0.685") + arb("0.155") * L.log())


def nu_littlewood(L, Z2="21.233"):
    return L.log() / (arb(Z2) * L)


NU = {"classical": nu_classical, "ford": nu_ford, "littlewood": nu_littlewood}


def nu_of(name, L):
    if isinstance(name, str):
        return NU[name](L)
    return name(L)  # user callable arb->arb


# ---------------------------------------------------------------- analytic pieces
def BTZ(r, l):
    return (l + arb("4.709774")) / (4 + 8 * r) + (4 / PI - 1) * (1 + 1 / r).log() / (1 + 2 * r) + arb("2.6908")


USE_WEYL = [False]


def BTZ_used(r, l):
    """the bound for -J used by Lemma B: TZ's BTZ, or (if USE_WEYL) min(BTZ, BTZW) (Lemma B-W)."""
    b = BTZ(r, l)
    if USE_WEYL[0]:
        from lemmaB_weyl import BTZW
        bw = BTZW(r, l)
        return bw if bw.upper() < b.upper() else b
    return b


def mzeta_logder(r):
    """-zeta'/zeta(1+r) (Arb, r>0 point or ball)."""
    c = arb_series([1 + r, 1], prec=2).zeta().coeffs()
    return -c[1] / c[0]


# ---------------------------------------------------------------- trigonometric polynomial
def check_trig_nonneg(a0, ak):
    """Rigorously check P(theta) = a0 + cos th + sum_k ak[k] cos(k th) >= 0 (all theta), K<=3,
    by writing P as a polynomial in c=cos(theta) on [-1,1] and checking endpoints and critical points.
    a0, ak given as Fractions (exact). Returns the certified minimum (arb lower bound)."""
    K = max([1] + list(ak.keys()))
    assert K <= 3
    a2 = ak.get(2, Fr(0)); a3 = ak.get(3, Fr(0))
    # P = a0 + c + a2 (2c^2-1) + a3 (4c^3 - 3c)
    p = [a0 - a2, 1 - 3 * a3, 2 * a2, 4 * a3]  # coefficients of c^0..c^3 (exact)
    def ev(c):
        return arb(p[0].numerator) / p[0].denominator + c * (arb(p[1].numerator) / p[1].denominator
               + c * (arb(p[2].numerator) / p[2].denominator + c * (arb(p[3].numerator) / p[3].denominator)))
    cands = [arb(-1), arb(1)]
    # derivative: p1 + 2 p2 c + 3 p3 c^2
    A3 = 3 * p[3]; A2 = 2 * p[2]; A1 = p[1]
    if A3 != 0:
        disc = A2 * A2 - 4 * A3 * A1
        if disc >= 0:
            sd = arb(disc.numerator).sqrt() / arb(disc.denominator).sqrt()
            for sg in (1, -1):
                c = (-arb(A2.numerator) / A2.denominator + sg * sd) / (2 * arb(A3.numerator) / A3.denominator)
                if c.upper() >= -1 and c.lower() <= 1:
                    cands.append(c)
    elif A2 != 0:
        c = -arb(A1.numerator) / A1.denominator / (arb(A2.numerator) / A2.denominator)
        if c.upper() >= -1 and c.lower() <= 1:
            cands.append(c)
    vals = [ev(c) for c in cands]
    m = min(f_down(v) for v in vals)
    # the critical points are enclosed by balls; the value enclosure at a ball covers the true critical value.
    return m


def optimise_float(Z, L, hfac=1.0, K=3):
    """float LP: choose rho and (a0, a_k) minimising the box constant at delta = nu (worst case)."""
    from scipy.optimize import linprog
    best = None
    for rho in np.linspace(0.3, max(6.0, 2.0 * hfac), 141):
        nu = 1 / (Z * L); d = nu; r = rho * d; h = hfac * d
        fX = lambda X: X / (X * X + h * h / 4)
        cmin = min(fX(r + nu), fX(r + d)) - 4 * (r + d) / (1 + 2 * r) ** 2
        den = cmin * d * L
        if USE_WEYL[0]:
            bt = lambda l: min((l + 4.709774) / (4 + 8 * r), ((l + 0.3466) / 6 + math.log(0.618 * (l + 0.3466))) / (1 + 2 * r))                 + (4 / math.pi - 1) * math.log(1 + 1 / r) / (1 + 2 * r) + 2.6908
        else:
            bt = lambda l: (l + 4.709774) / (4 + 8 * r) + (4 / math.pi - 1) * math.log(1 + 1 / r) / (1 + 2 * r) + 2.6908
        c = np.array([(1 / r) / den] + [bt(L + math.log(k)) / den for k in range(2, K + 1)])
        th = np.linspace(0, math.pi, 4001)
        A = -np.column_stack([np.ones_like(th)] + [np.cos(k * th) for k in range(2, K + 1)])
        res = linprog(c, A_ub=A, b_ub=np.cos(th), bounds=[(0, None)] * K, method="highs")
        val = res.fun + bt(L) / den
        if best is None or val < best[0]:
            best = (val, rho, res.x)
    return best


def rationalise(xs, rho):
    """round LP solution to exact fractions; inflate a0 so that P>0 is certifiable."""
    a2 = Fr(round(xs[1] * 10000), 10000) if len(xs) > 1 else Fr(0)
    a3 = Fr(round(xs[2] * 10000), 10000) if len(xs) > 2 else Fr(0)
    ak = {}
    if a2: ak[2] = a2
    if a3: ak[3] = a3
    a0 = Fr(math.ceil(xs[0] * 10000) + 2, 10000)
    while check_trig_nonneg(a0, ak) <= 0:
        a0 += Fr(1, 10000)
    return a0, ak, Fr(round(rho * 100), 100)


# ---------------------------------------------------------------- rigorous box bound
def phi_box(X, hf):
    return X / (X * X + hf * hf / 4)


def nbox_over_lambda(lam_lo, lam_hi, La, Lb, rho, a0, ak, hfac, lam_min):
    """upper bound of #B/(delta L) for all lambda = delta*L in [lam_lo, lam_hi], L in [La, Lb],
    with r = rho*delta, h = hfac*delta (arb inputs; rho, hfac arb), where every zero in the box
    has 1 - beta >= nu(T) and nu(T) log T >= lam_min.  Uses monotonicity where noted."""
    d_lo = lam_lo / Lb; d_hi = lam_hi / La
    r_lo = rho * d_lo; r_hi = rho * d_hi
    assert f_up(r_hi) < 0.5
    # the box must lie in the disc |s - rho| < 1/2 (Heath-Brown/TZ radius r1 -> 1/2 + r)
    assert f_up(((r_hi + d_hi) ** 2 + (hfac * d_hi) ** 2 / 4).sqrt()) < 0.5
    # numerator: each term is decreasing in r (and BTZ increasing in L) -> evaluate at r_lo, Lb
    num = arb(a0.numerator) / a0.denominator * mzeta_logder(r_lo)
    for k, a in ak.items():
        aa = arb(a.numerator) / a.denominator
        num += aa * (BTZ_used(r_lo, Lb + arb(k).log()) + arb("1e-24"))
    num += BTZ_used(r_lo, Lb) + arb("1e-24")
    # c_min = min over X in [r+nu, r+delta] of X/(X^2 + h^2/4); with e = nu/delta in [e_lo, 1],
    #   delta * c_min >= G := min(phi(rho + e_lo), phi(rho + 1)),  phi(X) = X/(X^2 + hfac^2/4)
    # (phi is unimodal, so its minimum over an interval is attained at an endpoint).
    e_lo = arb(min(1.0, f_down(arb(lam_min) / lam_hi)))
    G = arb(min(f_down(phi_box(rho + e_lo, hfac)), f_down(phi_box(rho + 1, hfac))))
    # #B/(delta L) <= num / ((G/delta - 4(r+delta)/(1+2r)^2) * delta * L) <= num / ((G - 4(rho+1) delta^2) L)
    den = (G - 4 * (rho + 1) * d_hi ** 2) * La
    assert f_down(den) > 0
    return num / den


def cf_upper(alpha0, nu_name, L0, L1, hfac="1", K=3, lam_steps=200, L_steps=None, params=None, verbose=False, weyl=False):
    USE_WEYL[0] = bool(weyl)
    try:
        return _cf_upper(alpha0, nu_name, L0, L1, hfac, K, lam_steps, L_steps, params, verbose)
    finally:
        USE_WEYL[0] = False


def _cf_upper(alpha0, nu_name, L0, L1, hfac="1", K=3, lam_steps=200, L_steps=None, params=None, verbose=False):
    """Rigorous sup over log T in [L0,L1] and delta in [nu(T), 1-alpha0] of #B/(delta log T).
    Returns (cf arb, details)."""
    L0 = float(L0); L1 = float(L1)
    hf = arb(str(hfac))
    if L_steps is None:
        L_steps = max(1, int(math.ceil((L1 - L0) / 0.5)))
    # worst-case Z for the optimisation (smallest nu*L on the row)
    Ls = [L0 + (L1 - L0) * i / L_steps for i in range(L_steps + 1)]
    lam_min_all = min(f_down(nu_of(nu_name, arb(Lx)) * arb(Lx)) for Lx in Ls)
    if params is None:
        Zw = 1 / lam_min_all
        val, rho_f, xs = optimise_float(Zw, L0, float(hfac), K)
        a0, ak, rho = rationalise(xs, rho_f)
    else:
        a0, ak, rho = params
    rho_a = arb(rho.numerator) / rho.denominator
    trig_min = check_trig_nonneg(a0, ak)
    assert trig_min > 0
    worst = 0.0
    for La_, Lb_ in zip(Ls[:-1], Ls[1:]):
        La = arb(La_); Lb = arb(Lb_)
        # lambda_min on this L-piece: nu(L) L is monotone on each of our regions; take min of endpoint
        # values and, for safety, of an interval evaluation.
        lam_min = min(f_down(nu_of(nu_name, La) * La), f_down(nu_of(nu_name, Lb) * Lb),
                      f_down(nu_of(nu_name, arb(0.5 * (La_ + Lb_), 0.5 * (Lb_ - La_))) * arb(0.5 * (La_ + Lb_), 0.5 * (Lb_ - La_))))
        lam_max = (1 - float(alpha0)) * Lb_
        # geometric lambda grid (finer near lam_min where the sup is attained)
        q = (lam_max / lam_min) ** (1.0 / lam_steps)
        lams = [lam_min * q ** i for i in range(lam_steps + 1)]
        lams[-1] = lam_max
        for la, lb in zip(lams[:-1], lams[1:]):
            v = nbox_over_lambda(arb(la), arb(lb), La, Lb, rho_a, a0, ak, hf, lam_min)
            worst = max(worst, f_up(v))
    return arb(worst), dict(a0=a0, ak=ak, rho=rho, trig_min=trig_min)


def b1b2_upper(alpha0, nu_name, L0, L1, hfac="1", params=None):
    """Affine form  #B <= b1 * delta * log T + b2  valid for delta in [nu(T), 1-alpha0], log T in [L0,L1]
    (rigorous upper bounds for b1, b2 from the same lemma; see REPORT.md)."""
    cf, det = cf_upper(alpha0, nu_name, L0, L1, hfac=hfac, params=params)
    a0, ak, rho = det["a0"], det["ak"], det["rho"]
    rho_a = arb(rho.numerator) / rho.denominator; hf = arb(str(hfac))
    L0a = arb(float(L0)); L1a = arb(float(L1))
    # reviewer fix: interval evaluation (valid for any callable nu), on 40 sub-balls
    _pts = np.linspace(float(L0), float(L1), 41)
    lam_min = min(f_down(nu_of(nu_name, arb(0.5 * (a_ + b_), 0.5 * (b_ - a_) * (1 + 1e-12))) * arb(0.5 * (a_ + b_), 0.5 * (b_ - a_) * (1 + 1e-12)))
                  for a_, b_ in zip(_pts[:-1], _pts[1:]))
    d_min = arb(lam_min) / L1a; d_max = (1 - arb(str(alpha0)))
    r_min = rho_a * d_min
    lam_max = (1 - float(alpha0)) * float(L1)
    e_lo = arb(min(1.0, lam_min / lam_max))
    g = arb(min(f_down(phi_box(rho_a + e_lo, hf)), f_down(phi_box(rho_a + 1, hf))))
    gg = g - 4 * (rho_a + 1) * d_max ** 2
    sa = sum((arb(a.numerator) / a.denominator for a in ak.values()), arb(0))
    # b2 : a0 * delta * Z(rho delta) / gg <= a0 / (rho gg)   since r Z(r) = r(-zeta'/zeta(1+r)) < 1
    #      (Delange 1987: zeta'/zeta(s) > -1/(s-1) + 1/(2 s^2) for s > 1)
    b2 = arb(a0.numerator) / a0.denominator / (rho_a * gg)
    # b1 : the rest divided by delta L
    const = (1 + sa) * (arb("4.709774") / 4 + (4 / PI - 1) * (1 + 1 / r_min).log() + arb("2.6908") + arb("1e-24"))
    for k, a in ak.items():
        const += arb(a.numerator) / a.denominator * arb(k).log() / 4
    b1 = ((1 + sa) / 4 + const / L0a) / gg
    return b1, b2, cf, det


if __name__ == "__main__":
    import sys
    sys.path.insert(0, ".")
    from bellotti_rows import rows
    for (L0, L1, nm) in ((math.log(3e12), 29, "classical"), (46.2, 50, "ford"), (80, 90, "ford")):
        r = [x for x in rows if abs(x["L0"] - L0) < 1e-6][0]
        cf, det = cf_upper(r["alpha0"], nm, L0, L1)
        nu0 = nu_of(nm, arb(L0))
        old = r["b1"] + r["b2"] / f_down(nu0 * arb(L0))
        print(f"[{L0:.2f},{L1}] {nm}: cf_new <= {f_up(cf):.4f}   Bellotti cf = b1 + b2/(nu(T0)L0) = {old:.4f}   ratio {f_up(cf)/old:.4f}   params {det}")
