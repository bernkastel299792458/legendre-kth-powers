"""Core of the height-dependent Littlewood zero-free region (thesis method, our own proof).

Notation (REPORT.md §2): v = log t, l(t) = log log t / log t, profile Z(v) piecewise constant, A(v) = 1/Z(v).
For a hypothetical zero rho0 = 1 - eta + i t violating the s+eps profile we use
    sigma* = 1 - y,  y = s * A_w * l(K t + T0)     (A_w = min of A over heights [t - T0, K t + T0])
    lambda = sigma* - sigma_n                       (zeta bounded ON the line sigma_n: HPY n=3, Yang n>=4)
and the contradiction condition (REPORT.md (C)):
    eta_max * Psi(t) < G(mu_low).
Everything returned by `cell_margin` is a rigorous arb enclosure over the whole v-cell.

All arithmetic is python-flint arb (ball arithmetic).  Floats are used only to choose parameters.
"""
from fractions import Fraction
from flint import arb, acb, ctx

ctx.prec = 128

# ----------------------------------------------------------------------------- parameters
THETA = arb('1.1272')          # Heath-Brown weight parameter (thesis (3.10)); any theta works
K = 16                         # degree of the trigonometric polynomial
T0 = arb(10) ** 10             # window half-width (thesis Def. 3.3)
EPS = arb('1e-100')            # induction step
S0 = arb('0.5')                # induction start: s >= S0 always (REPORT.md §2; base case needs every Z >= S0*21.233)
H_RH = 3 * arb(10) ** 12       # RH verified to height H (Platt-Trudgian 2021)
GAMMA = arb.const_euler()
PI = arb.pi()
LOG16 = arb(16).log()

# P(x) = |sum_j c_j e^{ijx}|^2 / 14912370 = sum_k a_k cos kx >= 0  (thesis §2.4 / BTY; a_0 = 1)
C_COEF = [4, -8, 2, 20, -9, -34, 27, 91, -27, -201, 32, 895, 1949, 2389, 1896, 949, 239]
_D = 14912370
A_FRAC = [Fraction(sum(C_COEF[j] * C_COEF[j + k] for j in range(K + 1 - k)) * (1 if k == 0 else 2), _D)
          for k in range(K + 1)]
assert A_FRAC[0] == 1
A_K = [arb(f.numerator) / f.denominator for f in A_FRAC]
A_SUM = sum(A_K[1:], arb(0))                     # a = sum_{k>=1} a_k = 2919857/828465
LOGK = [arb(0)] + [arb(k).log() for k in range(1, K + 1)]

# zeta bounds ON lines (all refereed):  |zeta(sig_n + i y)| <= X y^Y log y   (y >= 3)
#   n = 3: sig = 1/2, Hiary-Patel-Yang, JNT 256 (2024):     0.618 y^(1/6) log y
#   n >= 4: sig_n = 1 - n/(2^n - 2), Yang, JMAA 534 (2024), Thm 1.1:  1.546 y^(1/(2^n-2)) log y
LINES = {3: (arb(1) / 2, arb('0.618'), arb(1) / 6)}
for _n in range(4, 19):
    LINES[_n] = (1 - arb(_n) / (2 ** _n - 2), arb('1.546'), arb(1) / (2 ** _n - 2))


# ----------------------------------------------------------------------------- weight w
def _sec(x): return 1 / x.cos()


def _cot(x): return 1 / x.tan()


D_SUPP = 2 * THETA * _cot(THETA)                 # supp w = [0, 2 theta cot theta]


def w0(theta=THETA):
    """w(0) = sec^2 th (th tan th + 3 th cot th - 3)  (closed form, checked against w(0) in check_core.py)."""
    return _sec(theta) ** 2 * (theta * theta.tan() + 3 * theta * _cot(theta) - 3)


W0 = w0()


def w_acb(u):
    """Heath-Brown weight (thesis Def. 3.1), analytic in u (acb), for 0 <= u <= 2 th cot th."""
    t = acb(THETA)
    tn = t.tan(); ct = 1 / tn; s2 = 1 / t.cos() ** 2
    return s2 * (s2 * (t * ct - u / 2) * (u * tn).cos() + 2 * t * ct - u
                 + (2 * t - u * tn).sin() / (2 * t).sin() - 2 * (1 + (t - u * tn).sin() / t.sin()))


def G_of_mu(mu, deriv=0):
    """G(mu) = int_0^d e^{mu u}(a1 e^{-u} - a0) w(u) du   (= a1 F(sigma*-beta0) - a0 F(sigma*-1), exact).
    deriv = 1 gives G'(mu).  mu: arb (may be a ball)."""
    a0, a1 = acb(A_K[0]), acb(A_K[1])
    m = acb(mu)

    def f(u, analytic):
        r = (m * u).exp() * (a1 * (-u).exp() - a0) * w_acb(u)
        return r * u if deriv else r
    return acb.integral(f, 0, acb(D_SUPP)).real


# ----------------------------------------------------------------------------- Ford's W0 bound
def C_ford(nu, r, theta=THETA):
    """|W0(z)| <= C(nu, r)|z|^-3 for Re z >= nu, |z| >= r > tan theta  (Ford 2002 §7, constants as corrected in
    arXiv:1910.08205; c0 = 1/(sin th cos^3 th) -- the thesis/BTY print a typo, see proof/zfr_audit)."""
    t = theta
    tn = t.tan()
    c0 = 1 / (t.sin() * t.cos() ** 3)
    c1 = (t - t.sin() * t.cos()) * tn ** 4
    c2 = tn ** 3 * t.sin() ** 2
    c3 = (t - t.sin() * t.cos()) * tn ** 2
    assert r > tn, "C_ford needs r > tan(theta)"
    return c0 * r * (c2 * (r + 1) ** 2 * ((-2 * nu * t * _cot(t)).exp() + 1) + c1 * r + c3 * r ** 3) / (r ** 2 - tn ** 2) ** 2


# ----------------------------------------------------------------------------- zero counting (Rosser 1941, Thm 19)
def R0_log(logT):
    """Rosser 1941 Thm 19: |N(T) - (T/2pi) log(T/2pi e) - 7/8| <= R0(T) = 0.137 log T + 0.443 log log T + 1.588
    (T >= 2).  Argument: log T."""
    return arb('0.137') * logT + arb('0.443') * logT.log() + arb('1.588')


LOG2PI = (2 * PI).log()


def M_strip(logT):
    """#{rho: |gamma - T| <= 1} <= (1/pi) log(T/2pi) + 2 R0(T) + 1e-9   (thesis (3.33); REPORT §4.3)."""
    return (logT - LOG2PI) / PI + 2 * R0_log(logT) + arb('1e-9')


def S_far(logT):
    """sum_{|gamma - T| > 1} |gamma - T|^-3 <= (1/2pi) log(T/2pi) + 4 R0(T) + 1e-9  (thesis Lemma 3.12; REPORT §4.3)."""
    return (logT - LOG2PI) / (2 * PI) + 4 * R0_log(logT) + arb('1e-9')


# ----------------------------------------------------------------------------- the per-cell inequality
KAPPA_Q = (PI.log() - (2 - GAMMA - 2 * arb(2).log())) / 2    # (log pi - psi(3/2))/2 = 0.55411...
PSI_EXTRA = arb(10) / 3                                         # |Re psi(1/4+iy/2)| <= log(|y|/2+4) + 10/3


def ell(v):
    """l(t) = log log t / log t as a function of v = log t."""
    return v.log() / v


def logKt(v):
    """log(K t + T0) for v = log t."""
    return v + (K + T0 * (-v).exp()).log()


def E_coef(x0, eta):
    """C = C(x0/eta, x0/eta): |W0((s - 1/2 - iy)/eta)| <= C eta^3 |s - 1/2 - iy|^-3 when Re s - 1/2 >= x0."""
    nu = x0 / eta
    return C_ford(nu, nu)


def E_bound(C, x0, logT, eta):
    """Upper bound for |E(s)|, s = sigma + iT, sigma - 1/2 >= x0 > 0 (REPORT §4.5); logT = None means T = 0:
       |E(s)| <= (C/2pi) eta^3 [ (2/x0^2)(log(T/2+4) + 10/3) + 2/(x0 (T+8)) ] + C eta^3/x0^3."""
    if logT is None:
        main = (2 / x0 ** 2) * (arb(4).log() + PSI_EXTRA) + 2 / (x0 * 8)
    else:
        T = logT.exp()
        main = (2 / x0 ** 2) * ((T / 2 + 4).log() + PSI_EXTRA) + 2 / (x0 * (T + 8))
    return C / (2 * PI) * eta ** 3 * main + C * eta ** 3 / x0 ** 3


def cell_terms(va, vb, Z, Zw, n, detail=False):
    """Rigorous enclosures for all t with log t in [va, vb]: band constant Z (A = 1/Z), window constant
    Zw = max of Z over the window (A_w = 1/Zw), zeta bound on line n.
    Returns (mu_low, PsiEta[, details]) with mu_low a lower bound for mu = (1-sigma*)/eta and PsiEta an arb ball
    whose upper end bounds eta * Psi.  The cell is certified iff PsiEta.upper() < G(mu_low).lower().
    Returns None if the parameter constraints (3/4 < sigma* < 1, 1 - sigma* < lambda < 1/2) fail."""
    va, vb = arb(va), arb(vb)
    v = (va + vb) / 2
    v = arb(v.mid(), ((vb - va) / 2).upper() * (1 + arb('1e-30')).upper())   # ball covering [va, vb]
    A = 1 / arb(Z)
    Aw = 1 / arb(Zw)
    sig_n, X, Y = LINES[n]
    LK = logKt(v)
    lK = LK.log() / LK
    lt = ell(v)
    # worst case s = 1 for y (B and the error terms increase with y; REPORT §4.1)
    y = Aw * lK
    sig = 1 - y
    lam = sig - sig_n
    ok = (lam.upper() < arb('0.5').lower()) and ((lam - y).lower() > 0) and (sig.lower() > arb('0.75').upper())
    if not ok:
        return None
    eta_max = (1 + 2 * EPS / S0) * A * lt                      # eta <= (s+eps) A l(t) <= (1+2eps/S0)... * A l(t)
    # ---- main term  B (REPORT §4.1): (1/2lam)[ sum_k a_k (log X + Y log(kt) + loglog(kt)) + a0 log zeta(sig+lam) ]
    s_left = arb(0)
    for k in range(1, K + 1):
        lT = v + LOGK[k]
        s_left += A_K[k] * (X.log() + Y * lT + lT.log())
    x = sig + lam - 1
    B = (s_left + A_K[0] * (GAMMA * x - x.log())) / (2 * lam)
    # ---- zero sums, Lemmas 3.12-3.17 (REPORT §4.3)
    nu = lam / eta_max                                           # |z - rho| > lam  =>  |(z-rho)/eta| >= nu
    nu_l = arb(nu.lower())
    if not nu_l > 2 * THETA.tan():           # Ford's bound needs r > tan(theta); require some room
        return None
    Cm1 = C_ford(arb(-1), nu_l)
    sig1 = arb(sig.lower())
    J = (lam ** -3 + (2 * sig1 - 1 - lam) ** -3) / 2
    zsum = arb(0)
    for k in range(1, K + 1):
        lT = v + LOGK[k]
        zsum += A_K[k] * (J * M_strip(lT) + S_far(lT))
    zero_err = Cm1 * eta_max ** 3 * zsum                         # >= the k>=1 zero-sum error (times a_k summed)
    # ---- E-terms, Lemmas 3.19 / 3.20 (REPORT §4.5)
    x0 = arb((sig - arb(1) / 2).lower())
    CE = E_coef(x0, arb(eta_max.upper()))
    Esum = A_K[0] * E_bound(CE, x0, None, eta_max)
    for k in range(1, K + 1):
        Esum += A_K[k] * E_bound(CE, x0, v + LOGK[k], eta_max)
    # ---- mu_low and G
    mu_low = (Aw / A) * (lK / lt) * (1 - 4 * EPS / S0)
    mu_low = arb(mu_low.lower())
    # ---- (3.51): a1 (F - F*)(sigma*-beta0) <= a1 eta w0 (pi/2lam) 0.36 u,  u = pi(eta - y)/(2 lam) <= pi eta (1-mu_low)/(2 lam)
    u = PI * eta_max * (1 - mu_low) / (2 * lam)
    assert u.upper() < 1
    loss351 = A_K[1] * eta_max * W0 * (PI / (2 * lam)) * arb('0.36') * u
    # ---- tiny terms: Lemma 3.15 far zeros, Lemma 3.18, Lemma 3.20 tail (|gamma| > H): total <= 1e-9 eta
    tiny = arb('1e-9') * eta_max
    Psi_eta = eta_max * W0 * (B - A_K[0] * KAPPA_Q) + zero_err + Esum + loss351 + tiny
    return (mu_low, Psi_eta, dict(B=B, lam=lam, y=y, eta=eta_max, zero_err=zero_err, Esum=Esum,
                                  loss351=loss351, nu=nu_l, Cm1=Cm1, J=J)) if detail else (mu_low, Psi_eta)
