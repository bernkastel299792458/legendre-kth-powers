"""
Rigorous (Arb) re-implementation of the Kadiri--Lumley--Ng zero-density bound
(KLN, JMAA 465 (2018); arXiv:2101.12263v1, Lemma 4.14, eqs. (4.72)-(4.73)),
in three variants:

  "KLN"        : the original (Lemma 4.3 with (log X)^2, b4 = 0.529 tau^2 form);
                 N(s,T) <= A (log kT)^{2s} (log T)^{5-4s} T^{8(1-s)/3} + B log^2 T.
  "CS_literal" : Chourasiya--Simonic sec. 6 / eq. (119) as we believe it was computed:
                 KLN Lemma 4.3 replaced by CS Lemma 7 (one power of log X, no tau^2,
                 b4 = 0.54), everything else of (4.72) unchanged.
  "CS"         : the same, but with the factor e^{2d(2loglogH0 - loglog kH0)/logH0}
                 of (4.72) replaced by the one that the modified proof actually gives,
                 e^{4d loglogH0/logH0}  (AUDIT, see REPORT sec. 3.3).
For the CS variants:
     N(s,T) <= A log(kT) (log T)^{5-4s} T^{8(1-s)/3} + B log^2 T.

All quantities are arb balls; A is increasing in s and B decreasing in s, so a
row [s1,s2] uses A(s2), B(s1) (this monotonicity is checked numerically in
run_kln_tables.py at the row end points and mid points).
"""
from flint import arb, arb_series, ctx
import math

ctx.prec = 160
PI = arb.pi()
GAMMA = arb.const_euler()
LOG2 = arb(2).log()
E = arb(1).exp()
M0 = (1 + arb(2) / 3 * (arb(6) / 5).sqrt()).sqrt()
B1c, B2c, B3c = arb("0.62"), arb("1.048"), arb("0.605")


def rpow(x, e):
    return (e * x.log()).exp()


def amax(*xs):
    m = xs[0]
    for x in xs[1:]:
        m = m.max(x)
    return m


def gamma_derivs(z, n):
    """[Gamma(z), Gamma'(z), ..., Gamma^{(n)}(z)] as arb."""
    s = arb_series([z, 1], prec=n + 1)
    g = s.gamma()
    co = g.coeffs()
    return [co[k] * math.factorial(k) for k in range(n + 1)]


def I_int(A, n, alpha):
    """I(A,n) = int_0^oo x^A e^{-2 alpha x^2} (log x)^n dx  (KLN (4.20), beta = 2)."""
    z = (A + 1) / 2
    gd = gamma_derivs(z, n)
    l2a = (2 * alpha).log()
    s = arb(0)
    for j in range(n + 1):
        s += math.comb(n, j) * (-l2a) ** j * gd[n - j]
    return rpow(2 * alpha, -(A + 1) / 2) * s / arb(2) ** (n + 1)


def b6(X, eta):
    L = X.log()
    return (1 + eta) * L / (eta * rpow(X, eta)) * (1 + 1 / (eta * L) + GAMMA / L
                                                     + 7 * eta / (12 * (1 + eta) * X * L))


def b11(X, tau):
    L = X.log()
    t = tau - 1
    return 1 + 3 / (t * L) + 6 / (t * L) ** 2 + 6 / (t * L) ** 3


class KLN:
    def __init__(self, H0, k=arb(1), a1=arb("0.63"), a2=arb("2.851"), b4=arb("0.529"),
                 variant="KLN", H=None, b6X=arb(10) ** 9):
        self.H0, self.k, self.a1, self.a2, self.b4 = H0, k, a1, a2, b4
        self.variant = variant
        self.H = H0 - 1 if H is None else H
        self.kH0 = k * H0
        self.b6X = b6X          # KLN use b6(10^9, eta) in Cor. 4.11
        L = self.kH0.log()
        self.C1 = 6 / PI ** 2 + B2c / L
        self.C2 = PI * M0 * B1c / L + 6 * M0 / (PI * self.kH0) + PI * M0 * B2c / (self.kH0 * L)
        a3 = -6 * a1 / E + a2
        self.C3 = a3 ** 2 * self.C1 * L
        self.C4 = self.C1 * a1 ** 2 * (1 + 1 / self.C3.sqrt()) ** 2

    # --- F_X at sigma_2 = 1 + delta/log X -------------------------------------
    def C5C6(self, delta):
        L = self.kH0.log()
        if self.variant == "KLN":
            C5 = PI * M0 * self.b4 / (2 * delta) * (1 + 2 * delta / L) ** 2 * (2 * delta * GAMMA / L).exp()
            C6 = self.b4 / (5 * delta * delta.exp()) * (1 + delta / L) ** 2 + B3c * (-2 * delta).exp() / L ** 2
        else:  # CS Lemma 7: C3(X0,delta), C4(X0,delta)
            C5 = PI * M0 * self.b4 / (2 * delta) * (2 * delta * GAMMA / L).exp()
            C6 = self.b4 / (5 * delta * delta.exp()) + B3c * (-2 * delta).exp() / L
        return C5, C6

    def J(self, alpha, T):
        I = lambda A, n: I_int(A, n, alpha)
        r = self.C2 / self.C1 * self.k
        lT = T.log()
        a1, a2 = self.a1, self.a2
        b = arb(2)
        t3 = arb(1) / 3
        t6 = arb(1) / 6
        J = I(b + t3, 0) + r * I(b - 2 * t3, 0) \
            + (2 * I(b + t3, 1) + 2 * r * I(b - 2 * t3, 1)) / lT \
            + (I(b + t3, 2) + r * I(b - 2 * t3, 2)) / lT ** 2 \
            + 2 * a2 * (I(b + t6, 0) + r * I(b - 5 * t6, 0)) / (a1 * rpow(T, t6) * lT) \
            + 2 * a2 * (I(b + t6, 1) + r * I(b - 5 * t6, 1)) / (a1 * rpow(T, t6) * lT ** 2) \
            + a2 ** 2 * (I(b, 0) + r * I(b - 1, 0)) / (a1 ** 2 * rpow(T, 2 * t3) * lT ** 2)
        # coefficients must be positive for U to decrease in T (KLN remark, sec. 5)
        coeffs = [2 * I(b + t3, 1) + 2 * r * I(b - 2 * t3, 1), I(b + t3, 2) + r * I(b - 2 * t3, 2),
                  I(b + t6, 0) + r * I(b - 5 * t6, 0), I(b + t6, 1) + r * I(b - 5 * t6, 1)]
        return J, all(bool(c > 0) for c in coeffs)

    def U(self, alpha, T):
        omega1 = (alpha * (arb(1) / 2 / T) ** 2).exp()
        J, pos = self.J(alpha, T)
        return 4 * alpha * 2 * self.C4 * omega1 ** 2 * J, pos

    def V(self, alpha, delta, T):
        C5, C6 = self.C5C6(delta)
        sig2 = 1 + delta / (self.k * T).log()
        omega1 = (alpha * (sig2 / T) ** 2).exp()
        K = (C5 + C6 * PI * M0 / (self.k * T)) * I_int(arb(1), 0, alpha) + C6 / self.k * I_int(arb(2), 0, alpha)
        return 8 * alpha * omega1 ** 2 * K

    def Mkd(self, delta):
        return amax(self.H0.log() / (self.kH0.log() + 2 * delta), arb(1))

    def calC1(self, alpha, d, delta, sigma):
        H0, kH0 = self.H0, self.kH0
        lH0, lkH0 = H0.log(), kH0.log()
        b12 = 1 / (2 * (1 - 1 / self.H) ** 2)
        U, pos = self.U(alpha, H0)
        V = self.V(alpha, delta, H0)
        ex1 = (arb(8) / 3 * delta * (2 * sigma - 1) * self.Mkd(delta)
               + 4 * delta * (2 * sigma - 1) * lH0.log() / (lkH0 + 2 * delta)).exp()
        eU = 2 * (1 - sigma) + 2 * d / lH0 + 2 * delta * (2 * sigma - 1) / (lkH0 + 2 * delta)
        if self.variant in ("KLN", "CS_literal"):
            ex2 = 2 * d * (2 * lH0.log() - lkH0.log()) / lH0
        else:
            ex2 = 4 * d * lH0.log() / lH0
        val = b12 * ex1 * rpow(U, eU) * rpow(V, 2 * sigma - 1) * (ex2 + 8 * d / 3 + 2 * alpha).exp()
        checks = dict(U_gt_1=bool(U > 1), V_gt_1=bool(V > 1), J_coeffs_pos=pos,
                      delta_lt=bool(delta < lH0 * (lH0.log() - 1) / 2))
        return val, checks

    # --- C2 = C7 (mu - s + d/log H0) + C8 ---------------------------------------
    def C7(self, eta):
        H0, H, kH0 = self.H0, self.H, self.kH0
        z1 = (1 + eta).zeta()
        z2 = (2 + 2 * eta).zeta()
        b5 = z1 ** 4 / z2 ** 2 + 2 * z1 ** 2 / z2
        b7 = (1 + 2 / (arb("3.006") * z1 * rpow(kH0, 1 + eta))) * (arb("3.006") * z1) ** 2
        b8 = ((2 + eta) ** 2 / H ** 2 + ((1 + 2 * eta) / H + 1) ** 2).sqrt()
        b6v = b6(self.b6X, eta)
        b9 = PI * b7.log() / LOG2 + PI * b5.log() / LOG2 - 2 * PI * (1 - b6v ** 2).log() / LOG2 + PI \
            + 2 * (1 + 2 * eta) / LOG2 * (b8 / (2 * PI)).log()
        return (2 * (1 + 2 * eta) + 2 * PI * (1 + eta)) / LOG2 + b9 / H0.log(), bool(b6v < 1)

    def C8(self, mu):
        kH0, k = self.kH0, self.k
        b6v = b6(kH0, mu - 1)
        b10 = -(1 - b6v ** 2).log() / b6v ** 2
        return b10 * kH0.log() ** 2 / rpow(kH0, 2 * mu - 2) * (
            4 * mu * b11(kH0, 2 * mu) / (k * (2 * mu - 1))
            + 2 * PI * M0 * (2 * mu - 1) * b11(kH0, 2 * mu - 1) / (mu - 1))

    def C8_CT19(self, mu):
        """AUDIT: C8 with KLN (3.13) replaced by Cully-Hugill--Trudgian (Ramanujan J. 56
        (2021)) Thm 2 (arXiv:1911.07369v1):  sum_{n<=x} d(n)^2 <= x(D1 L^3+D2 L^2+D3 L+D4)
        + 9.73 x^{3/4} L + 0.73 x^{1/2}, x >= 2, as done by Cully-Hugill--Johnston (IJNT 2023,
        Lemma 7.1) and (we infer) by CS for B in Table 4.  Only k = 1 is supported.
        Partial summation: sum_{n>X} d^2 n^{-tau} <= tau int_X^oo D(t) t^{-tau-1} dt.
        Then int_H^T |f_X(mu+it)|^2 <= T S(2mu,X) + 2 pi m0 S(2mu-1,X) =: W(X) with X = T,
        and W(X)/log X is decreasing for log X >= 5 (each term is X^{-a} (log X)^{j-1}
        with a >= 2mu-2 >= 0.47, j <= 3), so C8 = b10 * W(H0)/log H0."""
        assert bool(self.k == 1)
        X = self.kH0
        LX = X.log()
        D1 = 1 / PI ** 2
        # exact values of D2, D3, D4 (upper ends; all enter with + sign)
        D2, D3, D4 = arb("0.74434128"), arb("0.82326521"), arb("0.46032338")

        def G(kk, c):
            s = arb(0)
            for j in range(kk + 1):
                s += math.factorial(kk) // math.factorial(kk - j) * LX ** (kk - j) / (c - 1) ** (j + 1)
            return rpow(X, 1 - c) * s

        def S(tau):
            return tau * (D1 * G(3, tau) + D2 * G(2, tau) + D3 * G(1, tau) + D4 * G(0, tau)
                          + arb("9.73") * G(1, tau + arb(1) / 4) + arb("0.73") * G(0, tau + arb(1) / 2))
        W = X * S(2 * mu) + 2 * PI * M0 * S(2 * mu - 1)
        b6v = b6(X, mu - 1)
        b10 = -(1 - b6v ** 2).log() / b6v ** 2
        return b10 * W / self.H0.log()

    def calC2(self, d, eta, mu, sigma, c8mode="KLN"):
        c7, ok = self.C7(eta)
        c8 = self.C8(mu) if c8mode == "KLN" else self.C8_CT19(mu)
        return c7 * (mu - sigma + d / self.H0.log()) + c8, ok

    def AB(self, alpha, d, delta, eta, mu, sig1, sig2, c8mode="KLN"):
        c1, chk = self.calC1(alpha, d, delta, sig2)
        c2, ok = self.calC2(d, eta, mu, sig1, c8mode)
        chk["b6<1"] = ok
        chk["sig>1/2+d/logH0"] = bool(sig1 > arb(1) / 2 + d / self.H0.log())
        chk["mu_range"] = bool(mu >= 1 + arb("0.23622") and mu <= 1 + eta)
        return c1 / (2 * PI * d), c2 / (2 * PI * d), chk


def max_zeta_half_0_3(n=6000):
    """Rigorous upper bound for max_{|t|<=3} |zeta(1/2+it)| (Arb, n subintervals)."""
    from flint import acb
    m = arb(0)
    for i in range(n):
        t = arb(3 * (2 * i + 1), 0) / (2 * n)
        tb = arb(t.mid(), arb(3) / (2 * n))
        z = acb(arb(1) / 2, tb).zeta()
        m = m.max(z.abs_upper())
    return m
