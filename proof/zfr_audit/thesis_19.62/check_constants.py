"""Check the numerical constants of thesis Ch. 3 (pp. 50-78) that do not involve
the main-term estimate: parameters (3.11), w(0), Ford constants, c_n of p. 78,
C4(mu0), the final inequality (p. 78), (3.50) and (3.51).

Run:  python -I check_constants.py  > check_constants_output.txt
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import *

out = []
def rep(name, val, claim=None, ok=None):
    s = f"{name:58s} = {fmt(val) if hasattr(val, 'mid') else val}"
    if claim is not None:
        s += f"   [thesis: {claim}]"
    if ok is not None:
        s += "   OK" if ok else "   ** FAIL **"
    print(s)

print("== Parameters (3.10)-(3.11), Definition 3.3 ==")
rep("theta", THETA, "1.1272")
W0 = w0()
rep("w(0) = sec^2 th (th tan th + 3 th cot th - 3)", W0)
rep("A1 = 1/19.62", A1, "0.05096...")
rep("sigma1 = sigma*(H1)", SIGMA1, "0.99648...", ok=abs(SIGMA1 - arb('0.99648')) < arb('1e-5'))
rep("eta1 = (A1+eps) loglog H1 / log H1", ETA1, "0.00363...", ok=abs(ETA1 - arb('0.00363')) < arb('1e-5'))
rep("lambda1 = lambda*(H1)", LAMBDA1, "0.49966...", ok=abs(LAMBDA1 - arb('0.49966')) < arb('1e-5'))
rep("lambda2 = lambda*(H2) (t>=H2 formula)", LAMBDA2, "0.29275...", ok=abs(LAMBDA2 - arb('0.29275')) < arb('1e-5'))
lam_H2_minus = lam4(LOG_H2)
rep("lambda*(H2-) (n=4 formula, min over [H1,H2))", lam_H2_minus, "0.27789...", ok=abs(lam_H2_minus - arb('0.27789')) < arb('1e-5'))
nu = lam_H2_minus / ETA1
rep("nu = 0.27789.../eta1  (p. 72 says lambda1/eta1 = nu = 76.36)", nu, "76.36...", ok=abs(nu - arb('76.36')) < arb('0.01'))
rep("   (lambda1/eta1 itself)", LAMBDA1 / ETA1, "text says = nu; it is not, but 76.36 is the valid (smaller) choice")
rep("sigma*(H2) - lambda*(H2) (t>=H2 formula)", sigma_star(LOG_H2) - LAMBDA2, "0.94475... in [s3,s4]",
    ok=False)
print("   -> true value lies in [sigma_3, sigma_4] = [0.5, 0.714]: the printed 0.94475 is a typo (cosmetic)")

print("\n== Trigonometric polynomial ==")
rep("a0", A_K[0], "1")
rep("a1", A_K[1], "865534/497079")
rep("a = sum_{k>=1} a_k", A_SUM, "2919857/828465")
print("   a = 2919857/828465 exactly:", A_FRAC and sum(A_FRAC[1:]) == Fraction(2919857, 828465))
print("   all a_k > 0:", all(f > 0 for f in A_FRAC))
S = sum((A_K[k] * arb(k).log() for k in range(2, K + 1)), arb(0))
rep("S = sum a_k log k", S)
rep("(a + S/log H1)/2   [coefficient in (3.21)]", (A_SUM + S / LOG_H1) / 2, "1.7761", ok=(A_SUM + S / LOG_H1) / 2 < arb('1.7761'))
rep("0.0069 * a", arb('0.0069') * A_SUM, "0.0244", ok=arb('0.0069') * A_SUM < arb('0.0244'))

print("\n== Ford constants C(nu, r) (Lemma 2.3) with theta = 1.1272 ==")
rep("tan(theta)", tan(THETA))
Cm1 = C_ford(arb(-1), nu); C0 = C_ford(arb(0), nu)
rep("C(-1, 76.36)", Cm1)
rep("C(0, 76.36)", C0)
print("   C(-1,nu) > C(0,nu) (needed p. 73):", Cm1 > C0)
rep("C(-1, H/eta1)  [Lemma 3.20 claims < 46]", C_ford(arb(-1), H / ETA1), "< 46", ok=C_ford(arb(-1), H / ETA1) < 46)
rep("C(-1, H1/eta1) [Lemma 3.18]", C_ford(arb(-1), LOG_H1.exp() / ETA1))

print("\n== Lemma 3.17: 18.6 C(-1,nu)(A1+eps)^2 L2'^2 log T / L1'^2 ... < 2.56 (loglog t)^2/log t ==")
# C1(T) <= 18.6 log T for lambda* >= 0.27789:
lamlo = lam_H2_minus
C1coef = arb('0.355') * (lamlo ** -3 + (2 * SIGMA1 - 1 - lamlo) ** -3) + 1
rep("0.355(l^-3 + (2 s1 - 1 - l)^-3) + 1 at l = 0.27789", C1coef, "<= 18.6", ok=C1coef < arb('18.6'))
# also at l = lambda1 (largest lambda) the bracket is smaller; check monotone endpoints
C1b = arb('0.355') * (LAMBDA1 ** -3 + (2 * SIGMA1 - 1 - LAMBDA1) ** -3) + 1
rep("   same at l = lambda1 = 0.49966", C1b, "<= 18.6", ok=C1b < arb('18.6'))
# C(-1,nu) eta^2 C1(T) <= 18.6 C(-1,nu) (A1+eps)^2 (L2'/L1')^2 ... with L2' < 1.012 L2, log T <= L1' (Kt+T0)
coef256 = arb('18.6') * Cm1 * (A1 + EPS) ** 2 * arb('1.012') ** 2
rep("18.6 C(-1,nu)(A1+eps)^2 1.012^2  [needs < 2.56]", coef256, "2.56", ok=coef256 < arb('2.56'))
rep("sum_k a_k (2.56 + 1e-10 L1/L2^2 ...) vs 0.75  (2.56*a/ L2^2*L1... see note)", arb('2.56') * A_SUM)
print("   note: p. 73 passes from eta*sum a_k(2.56 L2^2/L1) to 0.75 eta L1/L2^2; this needs")
print("   2.56 a L2^4/L1^2 <= 0.75, i.e. it is checked on a grid below.")
worst = arb(0)
L = arb('56.5')
while L < 226:
    L2 = L.log()
    v = arb('2.56') * A_SUM * L2 ** 4 / L ** 2 + A_SUM * arb('1e-10') * L2 ** 2 / L
    if v > worst: worst = v
    L += arb('0.5')
rep("max over [H1,H2] grid of 2.56 a L2^4/L1^2 (+1e-10 term)", worst, "<= 0.75", ok=worst < arb('0.75'))

print("\n== c_n, C4(mu0) (p. 78), theta = 1.1272 ==")
d = 2 * THETA * cot(THETA)
rep("2 theta cot theta", d)
a0, a1 = A_K[0], A_K[1]
u0 = (a1 / a0).log()        # sign change of a1 e^-u - a0
def integrand(n, absval=False):
    def f(u, analytic):
        v = u ** n * (acb(a1) * (-u).exp() - acb(a0)) * w_acb(u)
        return v
    return f
cn = []
for n in range(4):
    val = acb.integral(integrand(n), 0, acb(d)).real
    cn.append(val)
    rep(f"c{n}", val, ["0.8219901343", "0.1118643577", "0.0182350945", "-0.0003829770"][n])
cstar = (acb.integral(integrand(3), 0, acb(u0)).real - acb.integral(integrand(3), acb(u0), acb(d)).real)
rep("c* = int u^3 |a1 e^-u - a0| w", cstar, "0.0188374573")
mu0 = (1 - SIGMA1) / ETA1
rep("mu0 = (1 - sigma1)/eta1", mu0, "0.96454...")
def C4(m): return cn[0] + cn[1] * m + cn[2] / 2 * m ** 2 + (cn[3] / 6 - cstar / 18) * m ** 3
rep("C4(mu0) (thesis polynomial)", C4(mu0), "> 0.9376", ok=C4(mu0) > arb('0.9376'))
# The bound e^x >= 1+x+x^2/2+x^3/6 - x^4/18 with x = mu u <= 1.0712 does NOT give the
# coefficient c*/18 of mu^3 (it needs x <= 1). Exact value of the integral at mu0:
def I_exact(m):
    f = lambda u, an: (acb(m) * u).exp() * (acb(a1) * (-u).exp() - acb(a0)) * w_acb(u)
    return acb.integral(f, 0, acb(d)).real
rep("exact a1 W(1-mu0) - a0 W(-mu0)", I_exact(mu0), "> 0.9376", ok=I_exact(mu0) > arb('0.9376'))
# monotonicity on [mu0, 1]: derivative int u e^{mu u}(...)w on a grid of mu-balls
okmono = True
m = mu0
step = (1 - mu0) / 64
for i in range(64):
    ball = arb((m + m + step) / 2, step / 2 + arb('1e-30'))
    f = lambda u, an, b=ball: u * (acb(b) * u).exp() * (acb(a1) * (-u).exp() - acb(a0)) * w_acb(u)
    dv = acb.integral(f, 0, acb(d)).real
    if not dv > 0: okmono = False
    m += step
print("   d/dmu of the exact integral > 0 on [mu0,1] (64 mu-balls):", okmono)

print("\n== (3.50): C3(eta,t) = (0.75 L1/L2^2 + 2.9 L2/L1 - 2.9) eta,  eta <= (A1+eps) L2/L1 ==")
best = (arb(-1), None)
L = arb('56.5')
while L < 20000:
    L2 = L.log()
    v = (arb('0.75') * L / L2 ** 2 + arb('2.9') * L2 / L - arb('2.9')) * (A1 + EPS) * L2 / L
    if v > best[0]: best = (v, L)
    L *= arb('1.0005')
rep("max C3 over grid log t in [56.5, 2e4]", best[0], "0.00452... at log t = 1144.7")
rep("   at log t", best[1])
print("   (for log t > 2e4 the bound is < 0.75 A1/L2 < 0.0039)")

print("\n== (3.51): F*(sigma*-beta0) >= F(sigma*-beta0) - 1e-6 ==")
# x = pi (sigma*-beta0)/(2 lambda*), sigma*-beta0 <= (A1+eps)L2/L1 - A1 L2'/L1'  (>0)
def x_of(L):
    LK = logKt(L)
    z = (A1 + EPS) * L.log() / L - A1 * LK.log() / LK
    return PI * z / (2 * lam_star(L)), z
xH1, zH1 = x_of(LOG_H1)
rep("sigma*-beta0 upper bound at t = H1", zH1)
rep("x = pi(sigma*-beta0)/(2 lambda*) at H1", xH1, "< eps0 = 7e-5", ok=xH1 < arb('7e-5'))
print("   -> the printed bound uses (L2(Kt)/L1(Kt) - loglog t/log t), which is negative;")
print("      the correct difference has the opposite sign and is ~1.3e-4.")
# actual loss f(0)(pi/2lambda)(1/x - cot x) <= f(0)(pi/2lambda)(x/3 + x^3/45) ; eta<=eta1
worst = arb(0)
L = arb('56.5')
while L < 2000:
    x, z = x_of(L)
    eta = (A1 + EPS) * L.log() / L
    loss = eta * W0 * PI / (2 * lam_star(L)) * (1 / x - cot(x))
    if loss > worst: worst = loss
    L += arb('0.5')
rep("max over grid of f(0)(pi/2l)(1/x - cot x)  [thesis: < 1e-6]", worst, "< 1e-6", ok=worst < arb('1e-6'))
rep("   corresponding loss a1*max", a1 * worst)

print("\n== Final inequality (p. 78) ==")
C3max = arb('0.00452')
lhs = (arb('0.9376') - arb('1e-6') * a1 - C3max) / (arb('3.4431') * W0)
rep("(0.9376 - 1e-6 a1 - 0.00452)/(3.4431 w(0))", lhs, ">= 0.05098 > A1+eps", ok=(lhs > arb('0.05098')) and (arb('0.05098') > A1 + EPS))
lhs2 = (I_exact(mu0) - a1 * worst - best[0]) / (arb('3.4431') * W0)
rep("same with exact integral, corrected (3.51) loss, exact C3max", lhs2)
rep("A1 + eps", A1 + EPS)
rep("relative slack  lhs/(A1+eps) - 1", lhs / (A1 + EPS) - 1)
rep("largest main-term coefficient c allowed by the slack", (arb('0.9376') - arb('1e-6') * a1 - C3max) / ((A1 + EPS) * W0))
