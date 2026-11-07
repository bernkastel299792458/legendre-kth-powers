"""
Rigorous (Arb) re-implementation of Chourasiya--Simonic, arXiv:2507.15184v2,
Theorem 1 (sec. 2.1) and Corollary 1 / Table 1.

Every function returns arb balls.  Upper bounds that involve integrals use
rigorous monotone Riemann sums plus an explicit tail bound (see K1_integral).

Notation follows the paper (equation labels of the LaTeX source in brackets).
Inputs that are NOT from the paper are marked "AUDIT".
"""
from flint import arb, ctx

ctx.prec = 160

PI = arb.pi()
GAMMA = arb.const_euler()
LOG2 = arb(2).log()
# m0 = sqrt(1 + (2/3) sqrt(6/5))   (Lemma 5, KLN (3.15), Preissmann/Ramare)
M0 = (1 + arb(2) / 3 * (arb(6) / 5).sqrt()).sqrt()
B1c = arb("0.62")     # KLN (3.5), Ramare Lemma 3.1
B2c = arb("1.048")    # KLN (3.5), Ramare Lemma 3.4
B3c = arb("0.605")    # KLN (3.8), Ramare Lemma 5.6
B4_PAPER = arb("0.54")  # CS Lemma 7 (private communication, X >= 3e10)
H_RH = arb(3) * arb(10) ** 12  # CS: H_RH := 3e12 (Platt--Trudgian: 3.000175e12)


def amax(*xs):
    """Upper bound of the max of arb balls (returned as a ball containing max)."""
    m = xs[0]
    for x in xs[1:]:
        m = m.max(x)
    return m


def rpow(x, e):
    """x^e for x>0 (arb)."""
    return (e * x.log()).exp()


# ---------------------------------------------------------------------------
# Lemma 5 (KLN Lemma 4.1): int_0^T |M_X(1/2+it)|^2 <= (C1 T + C2 X) log X
def C1f(X0):
    return 6 / PI ** 2 + B2c / X0.log()


def C2f(X0):
    L = X0.log()
    return PI * M0 * B1c / L + 6 * M0 / (PI * X0) + PI * M0 * B2c / (X0 * L)


# Lemma 7: F_X(1+delta/logX, 0, T, 1/2) <= (C3 + C4 (T + pi m0)/X) log X
def C3f(X0, delta, b4):
    return PI * M0 * b4 / (2 * delta) * (2 * delta * GAMMA / X0.log()).exp()


def C4f(X0, delta, b4):
    return b4 / (5 * delta * delta.exp()) + B3c * (-2 * delta).exp() / X0.log()


# Lemma 8 (eq. C5)
def _q(u):
    return 1 + (2 + GAMMA + arb(7) / (36 * u)) / u.log()


def b6sq(u):
    """b6(u,1/2)^2 = 9 q^2 log^2 u / u  (KLN (4.45) with eta = 1/2)."""
    return 9 * _q(u) ** 2 * u.log() ** 2 / u


def C5f(u, h):
    q = _q(u)
    return (-(1 - b6sq(u)).log()) * (3 / h + 8 * PI * M0) * (1 + arb("3.31") / u.log()) \
        / (9 * q ** 2) * u.log()


# Lemma 9 (eq. C6), with the paper's constant 220 (default) or an override
def C6f(u, H0, const=arb(220)):
    b8 = ((arb(5) / (2 * H0)) ** 2 + (1 + 2 / H0) ** 2).sqrt()
    return const + PI / LOG2 * (1 + u ** arb(-1.5)).log() \
        + 4 / LOG2 * (b8 / (2 * PI)).log() \
        - 2 * PI / LOG2 * (1 - b6sq(u)).log()


def C6_const_derived():
    """AUDIT: the constant that KLN Cor. 4.11 / Lemma 4.12 actually give at
    eta = 1/2 (CS write 220):  (2pi/log2) log(3.006 zeta(3/2)) + (pi/log2) log b5(1/2) + pi."""
    z15 = arb(1.5).zeta()
    z3 = arb(3).zeta()
    b5 = z15 ** 4 / z3 ** 2 + 2 * z15 ** 2 / z3
    return 2 * PI / LOG2 * (arb("3.006") * z15).log() + PI / LOG2 * b5.log() + PI


# ---------------------------------------------------------------------------
# Corollary 4 (fourth moment), from Corollary 2 with T0 = 1e10
M1_1e10 = arb("34.842")
FM2_1e10 = arb("1.3897e16")
M2_1e10_2e10 = arb("9.5079e15")


def a1f(A0):
    L = (A0 / 2).log()
    return A0 * L ** 4 / (2 * PI ** 2) + M1_1e10 * A0 * L ** 3 + FM2_1e10


def a2f(A0):
    L = A0.log()
    r = 1 - LOG2 / L
    return r ** 4 / (2 * PI ** 2) + M1_1e10 / L * r ** 3 + M2_1e10_2e10 / (A0 * L ** 4)


# ---------------------------------------------------------------------------
def K1_integral(T0, kappa, h, N=6000, U=arb(120)):
    """Rigorous enclosure [lo, hi] of
       I = int_0^oo e^{-u} u^{1/6} (1 + log(1+3u/(4k))/(2 log T0))^{4/3}
                 (C1(hT0) sqrt(3u/(4k)) + h C2(hT0))^{2/3} du.
    P(u) := integrand * e^{u} is increasing, so on [u_i,u_{i+1}]
       P(u_i)(e^{-u_i}-e^{-u_{i+1}}) <= int <= P(u_{i+1})(e^{-u_i}-e^{-u_{i+1}}).
    Tail u >= U: log(1+x)<=x gives P(u) <= Kt (1+u)^{11/6}, and
       int_U^oo e^{-u}(1+u)^{11/6} du = e * Gamma(17/6, 1+U)."""
    X0 = h * T0
    c1, c2 = C1f(X0), C2f(X0)
    c = arb(3) / (4 * kappa)
    L2 = 2 * T0.log()

    def P(u):
        if u == 0:
            return arb(0)
        return rpow(u, arb(1) / 6) * rpow(1 + (1 + c * u).log() / L2, arb(4) / 3) \
            * rpow(c1 * (c * u).sqrt() + h * c2, arb(2) / 3)

    lo = arb(0)
    hi = arb(0)
    prevu = arb(0)
    prevP = arb(0)
    preve = arb(1)
    for i in range(1, N + 1):
        u = U * arb(i) ** 2 / arb(N) ** 2
        Pu = P(u)
        eu = (-u).exp()
        w = preve - eu
        lo += prevP * w
        hi += Pu * w
        prevu, prevP, preve = u, Pu, eu
    Kt = rpow(amax(arb(1), c / L2), arb(4) / 3) * rpow(c1 * c.sqrt() + h * c2, arb(2) / 3)
    # Gamma(s, z): python-flint convention z.gamma_upper(s)
    tail = Kt * arb(1).exp() * (1 + U).gamma_upper(arb(17) / 6)
    return lo, hi + tail


def thm1_constants(sig1, sig2, d, kappa, delta, A0, T0=None, H0=None, h=arb(1),
                   b4=B4_PAPER, c6const=arb(220), K1N=6000, verbose=False):
    """Constants A1..A5 of Theorem 1 (upper-bound balls) and the derived
    Corollary-1 constants B1, B2, B3 (for H = H0 = T0 = H_RH style use)."""
    if T0 is None:
        T0 = H_RH
    if H0 is None:
        H0 = H_RH
    X0 = h * T0
    lT0 = T0.log()
    llT0 = lT0.log()
    lX0 = X0.log()
    # hypotheses of Theorem 1
    hyp = {
        "H0>=1002": bool(H0 >= 1002),
        "T0>=max(e^2d,e^e)": bool(T0 > (2 * d).exp() and T0 > arb(1).exp() ** arb(1).exp()),
        "delta<=log(hT0)/20": bool(delta < lX0 / 20),
        "h>=3e10/T0": bool(h * T0 >= arb(3) * arb(10) ** 10),
        "sig1>1/2": bool(sig1 > arb(1) / 2),
        "sig2<=1": bool(sig2 <= 1),
        "A0>=1e10": bool(A0 >= arb(10) ** 10),
    }
    a1 = a1f(A0)
    a2 = a2f(A0)
    c1, c2 = C1f(X0), C2f(X0)
    c3, c4 = C3f(X0, delta, b4), C4f(X0, delta, b4)
    Ilo, Ihi = K1_integral(T0, kappa, h, N=K1N)
    pre = rpow(2 * a2 * (arb(3) / (4 * kappa)).sqrt(), arb(1) / 3)
    K1_second = rpow(2 * a1, arb(1) / 3) * rpow(h * c2 + A0 * c1 / T0, arb(2) / 3) \
        / (rpow(T0, arb(1) / 3) * rpow(lT0, arb(4) / 3))
    K1 = pre * Ihi + K1_second            # upper bound (K1 enters monotonically)
    K1lo = pre * Ilo + K1_second
    G32 = PI.sqrt() / 2                    # Gamma(3/2)
    K2 = rpow(arb(2), arb(1) / 3) * (arb(3) / (4 * kappa)).sqrt() * G32 \
        + rpow(arb(2), arb(1) / 3) * 4 * kappa / 3 * (A0 / T0) ** 3
    K3 = c3 + c4 / h * ((1 / (2 * kappa)).sqrt() * G32 + PI * M0 / T0)
    L0 = (kappa * (1 + ((1 + 2 * delta / lX0) / (4 * T0)) ** 2)).exp() / (1 - 1 / H0)
    e3 = 3 * delta / lX0
    L1 = amax(arb(1), rpow(K1, e3)) * amax(arb(1), rpow(K3, -e3)) * \
        (3 * delta * amax(arb(1), lT0 / lX0) + 4 * delta * amax(llT0 / lX0, llT0 / lT0)).exp()
    L2 = amax(arb(1), rpow(K2, e3)) * amax(arb(1), rpow(K3, -e3)) * \
        (3 * delta * amax(arb(1), lT0 / lX0)).exp()
    ed = 3 * d / lT0

    def mx(base, f):
        return amax(rpow(base, f(sig1)), rpow(base, f(sig2)))

    fL0 = lambda s: 2 / (2 - s)
    fK3 = lambda s: (2 * s - 1) / (2 - s)
    fK = lambda s: 3 * (1 - s) / (2 - s)
    A1 = L1 * (d * (3 + 4 * llT0 / lT0)).exp() * amax(arb(1), rpow(L0, -2 * d / lT0)) \
        * amax(arb(1), rpow(K3, -ed)) * amax(arb(1), rpow(K1, ed)) \
        * mx(L0, fL0) * mx(K3, fK3) * mx(K1, fK)
    A2 = L2 * (3 * d).exp() * amax(arb(1), rpow(K2, ed)) * amax(arb(1), rpow(L0, -2 * d / lT0)) \
        * amax(arb(1), rpow(K3, -ed)) * mx(L0, fL0) * mx(K3, fK3) * mx(K2, fK)
    par = (3 - 2 * sig1) / (2 * d) + 1 / lT0
    A3 = par / (PI * LOG2)
    A4 = 3 / (2 * LOG2) * par
    c5 = C5f(X0, h)
    c6 = C6f(X0, H0, c6const)
    A5 = c6 / (2 * PI) * par + c5 / (2 * PI * d)
    lH = H0.log()
    B1 = (A1 + A2 * rpow(lH, -6 * (1 - sig2) / (2 - sig2))) / (2 * PI * d)
    B2 = A3 + A4
    B3 = A3 * lH + A5
    out = dict(hyp=hyp, a1=a1, a2=a2, C1=c1, C2=c2, C3=c3, C4=c4, C5=c5, C6=c6,
               K1=K1, K1lo=K1lo, K2=K2, K3=K3, L0=L0, L1=L1, L2=L2,
               A1=A1, A2=A2, A3=A3, A4=A4, A5=A5, B1=B1, B2=B2, B3=B3)
    return out


TABLE1 = [
    # sig1, sig2, B1, B2, B3, d, kappa, delta, log10A0   (paper, Table 1, last two rows)
    ("0.93750", "0.96875", "35.35", "5.180", "91.86", "0.29", "0.09", "0.270", "11.42"),
    ("0.96875", "1.00000", "46.06", "4.897", "86.84", "0.29", "0.07", "0.303", "11.46"),
]


def row_params(row):
    s1, s2, B1, B2, B3, d, ka, de, lA = row
    return dict(sig1=arb(s1), sig2=arb(s2), d=arb(d), kappa=arb(ka), delta=arb(de),
                A0=rpow(arb(10), arb(lA))), (arb(B1), arb(B2), arb(B3))


if __name__ == "__main__":
    import sys
    print("m0 =", M0, " (paper: < 1.31541)")
    print("derived C6 constant (paper: 220):", C6_const_derived())
    for row in TABLE1:
        p, printed = row_params(row)
        print("=" * 78)
        print("Row sigma in [%s, %s]; d=%s kappa=%s delta=%s log10A0=%s" % (row[0], row[1], row[5], row[6], row[7], row[8]))
        for lab, b4 in (("b4=0.54 (paper, unpublished)", B4_PAPER),
                        ("b4=0.5936 (RZA v3 Thm1.2, X>=1e12, eps<=1/25)", arb("0.5936"))):
            o = thm1_constants(b4=b4, K1N=100000, **p)
            print("--", lab)
            print("   hypotheses:", o["hyp"])
            for k in ("a1", "a2", "C1", "C2", "C3", "C4", "C5", "C6", "K1lo", "K1", "K2", "K3",
                      "L0", "L1", "L2", "A1", "A2", "A3", "A4", "A5"):
                print("   %-4s = %s" % (k, o[k].str(10, radius=False)))
            for k, pv in zip(("B1", "B2", "B3"), printed):
                ok = "OK (printed >= computed)" if bool(o[k] <= pv) else "EXCEEDS printed"
                print("   %s = %s  printed %s  -> %s" % (k, o[k].str(8, radius=False), pv.str(6, radius=False), ok))
