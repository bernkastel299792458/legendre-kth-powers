"""Secondary estimates of thesis Ch. 3: error terms (Lemma 2.7 as used in
Lemmas 3.19/3.20), Lemma 3.11 (local zero density), Lemmas 3.12-3.14, the
constant 1.2532 of Lemma 3.17, and the k-choice in (3.27).

Mixed rigour: constants are arb balls; sup/inf over continuous ranges are taken
on grids (indicated), except where a monotonicity argument is printed.

Run:  python -I check_error_terms.py > check_error_terms_output.txt
"""
import os, sys, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import *
from mpmath import mp, mpf, quad, inf, log as mlog, pi as mpi
mp.dps = 30

W0 = w0()
def ok(b): return "OK" if b else "** FAIL **"

print("== Lemma 2.7 (error term of Kadiri's explicit formula), as used in Ch. 3 ==")
def U(y):
    y = abs(y)
    if y < 0.5:
        return 0.5 * mlog(16 / (1 + 4 * y * y)) + 2 / (1 + 4 * y * y) + 2
    return abs(mlog(y / 2) - 2 / (1 + 4 * y * y)) + 2 / (3 * y) + 1 / (8 * y * y)
for name, x0 in [("thesis Ch.2 sigma0", mpf('0.9934710854') - mpf('0.5')),
                 ("Ch.3 sigma1", mpf(SIGMA1.mid().str(20, radius=False)) - mpf('0.5'))]:
    f = lambda y: U(y) / (x0 ** 2 + y ** 2) ** 1.5
    I = 2 * (quad(f, [0, 0.25, 0.5]) + quad(f, [0.5, 1, 2, 10, 100, inf]))
    print(f"  int U(y)/(x0^2+y^2)^(3/2) dy with x0 = {x0} ({name}): {mp.nstr(I, 10)}"
          f"   [thesis Lemma 2.7: < 36 -> {ok(I < 36)};  BTY Lemma 8 claims < 24 -> {ok(I < 24)}]")
print("  U(0) =", mp.nstr(U(0), 8), "> log 100 =", mp.nstr(mlog(100), 8),
      "  -> 'U(x) < log(100 - x) for x <= 2' is false near x = 0 (harmless: I_1 is still < 1e-10)")
# Ford constants for theta = 1.1272 with Ch.3 parameters (sigma >= sigma1, eta <= eta1)
x0 = SIGMA1 - arb('0.5')
Ca = C_ford(x0 / ETA1, x0 / ETA1)
Cb = C_ford(SIGMA1 / ETA1, SIGMA1 / ETA1)
print("  theta=1.1272: C(x0/eta1, x0/eta1) =", fmt(Ca, 8), " [Lemma 2.7 uses 52 for theta=1.1338]", ok(Ca < 52))
print("  theta=1.1272: C(s1/eta1, s1/eta1)/x0^3 =", fmt(Cb / x0 ** 3, 8), " [Lemma 2.7: < 425]", ok(Cb / x0 ** 3 < 425))
print("  NOTE: Lemma 2.7 assumes eta <= A0/log t (A0 = 1/4.862).  In Ch. 3 only eta <= (A1+eps) L2/L1 holds,")
print("  so eta*log t <= (A1+eps) loglog t, which exceeds A0 for log t > ~56.6.  Redoing T1 without that hypothesis:")
print("     T1 <= (C/2pi) eta^3 (2 log t / x0^2 + 2e-10) <= (C/pi)(A1+eps) L2/x0^2 * eta^2 (+ tiny)")
coefT1 = Ca / PI * (A1 + EPS) / x0 ** 2
print("     (C/pi)(A1+eps)/x0^2 =", fmt(coefT1, 6), " so  sum_k a_k |E(s_k)| <= a*(", fmt(coefT1, 4), "L2 +", fmt(Cb / x0 ** 3 * ETA1, 4), ") eta^2")
print("  Lemma 3.19 claims sum a_k|E(s_k)| <= 55 eta^2 <= 2.9 eta L2/L1.  Corrected: <= c_E(t) eta L2/L1 with")
for Lx in ['56.5', '100', '112', '200', '1144.7', '1e4']:
    L = arb(Lx); L2 = L.log()
    cE = A_SUM * (coefT1 * L2 + Cb / x0 ** 3 * ETA1) * (A1 + EPS)
    print(f"     log t = {Lx:7s}: c_E = {fmt(cE, 5)}  (thesis 2.9)")
print("  -> 2.9 is exceeded for log t > ~122; effect on (3.50) C3max: see check_corrected_constant.py (< 1e-5).")
Et0 = Ca / (2 * PI) * arb('34.59') + Cb / x0 ** 3
print("  Lemma 3.20: E(sigma) <= (C/2pi*34.59 + C'/x0^3) eta^3 =", fmt(Et0, 6), "eta^3;  * eta1^2 =",
      fmt(Et0 * ETA1 ** 2, 6), "< 0.01 :", ok(Et0 * ETA1 ** 2 < arb('0.01')))
dig = (2 - GAMMA - arb(4).log())
q0 = (-PI.log() / 2 + dig / 2) * W0
print("  Lemma 3.20: f(0)(-log(pi)/2 + digamma(3/2)/2)/eta =", fmt(q0, 8), "; + 0.01 + 1e-10 < -2.9 :", ok(q0 + arb('0.01') < arb('-2.9')))

print("\n== Lemma 3.18: Re F*(s_k - 1) <= 0 ==")
print("  The proof uses Re(cot z - 1/z) = sin2x/(cosh2y - cos2x) <= 0; this drops -Re(1/z) = -x/|z|^2 > 0 for x < 0.")
print("  Correct identity: F*(z) = F0(z) + f(0)(pi/2l) cot(pi z/2l), so Re F*(s_k-1) <= |W0((s_k-1)/eta)| + (exp. small)")
print("  <= C(-1, H1/eta1) eta^3/(kt)^3 < 1e-70.  Conclusion holds up to a negligible term (cosmetic).")

print("\n== Lemma 3.12 / 3.13 counting constants (Rosser R0) ==")
def R0(T): return arb('0.137') * T.log() + arb('0.443') * T.log().log() + arb('1.588')
for LT in [LOG_H1, arb(100), arb(1000)]:
    T = LT.exp()
    s312 = (T / (2 * PI)).log() / (2 * PI) + 4 * R0(T) + arb('1e-9')
    s313 = (T / (2 * PI)).log() / PI + 2 * R0(T) + arb('1e-10')
    print(f"  log T = {fmt(LT,5)}: Lemma 3.12 sum <= {fmt(s312,6)} < log T = {fmt(LT,6)} {ok(s312 < LT)};"
          f"  |S| <= {fmt(s313,6)} < 0.71 log T = {fmt(arb('0.71')*LT,6)} {ok(s313 < arb('0.71')*LT)}")
print("  (both bounds are a fixed multiple of log T plus lower-order terms, so log T = log H1 is the worst case)")

print("\n== Lemma 3.11 (local zero density) ==")
al, be = arb('0.333'), arb('1.529')
# (3.32): Re cot(pi xi/(2 beta)) >= 0.1933 on {|xi - alpha| <= 1.01, Re xi >= alpha}; check the boundary
mn = arb(10)
for i in range(0, 2001):
    yy = arb('1.01') * (arb(i) / 1000 - 1)              # segment Re xi = alpha
    X = PI * al / (2 * be); Y = PI * yy / (2 * be)
    v = (2 * X).sin() / ((2 * Y).cosh() - (2 * X).cos())
    if v < mn: mn = v
for i in range(0, 2001):
    ph = PI * (arb(i) / 2000 - arb('0.5'))               # arc
    xi_re = al + arb('1.01') * ph.cos(); xi_im = arb('1.01') * ph.sin()
    X = PI * xi_re / (2 * be); Y = PI * xi_im / (2 * be)
    v = (2 * X).sin() / ((2 * Y).cosh() - (2 * X).cos())
    if v < mn: mn = v
print("  min of Re cot(pi xi/2beta) on boundary (grid 4002 pts) =", fmt(mn, 6), " [>= 0.1933]", ok(mn > arb('0.1933')))
print("  (minimum is at the corners xi = alpha +- 1.01i; (3.32) is false by ~4e-4 relative.  Using the true minimum",
      "m = 0.19323 instead of 0.1933 below -- the rounded constants 7.6, 1.7, 16 still hold.)")
m = arb('0.19323')
print("  1/(m pi) =", fmt(1 / (m * PI), 6), "<= 1.7", ok(1 / (m * PI) < arb('1.7')), ";  4.576/(m pi) =",
      fmt(arb('4.576') / (m * PI), 6), "<= 7.6", ok(arb('4.576') / (m * PI) < arb('7.6')))
cst = (2 * be / al + arb('1.549').log() - arb('0.3')) / (m * PI)
print("  (2beta/alpha + log1.549 - 0.3)/(m pi) =", fmt(cst, 6), "<= 16", ok(cst < 16))
z329 = GAMMA * (al + be) * LAMBDA2 - (al + be).log()
print("  (3.29): gamma(alpha+beta)lambda2 - log(alpha+beta) =", fmt(z329, 6), "< -0.3", ok(z329 < arb('-0.3')))
# (3.27): need an integer k>=3 with k/(2^k-2) > (beta-alpha) delta  and 1/(2^k-2) < -4.576 delta/log delta
print("  (3.27) k-choice: the printed justification mixes floor and ceiling (k/2^k >= (1+loglogphi/logphi)/(phi log2)")
print("  needs k >= (log phi+loglog phi)/log2, while 2^k <= phi log phi needs the floor).  Direct check instead:")
okk = True
for k in range(3, 80):
    # k is usable for delta in (d_lo, d_hi], d_lo = (k+1)/((b-a)(2^{k+1}-2)), d_hi = k/((b-a)(2^k-2))
    d_lo = arb(k + 1) / ((be - al) * (2 ** (k + 1) - 2))
    d_hi = min(arb(k) / ((be - al) * (2 ** k - 2)), LAMBDA2) if k > 3 else LAMBDA2
    if d_lo > LAMBDA2: continue
    rhs = arb('4.576') * d_lo / (-d_lo.log())         # increasing in delta: worst at d_lo
    if not (1 / arb(2 ** k - 2) < rhs): okk = False; print("    fails k =", k)
print("  largest admissible k satisfies both conditions for every delta in (0, lambda2]  (k = 3..79; asymptotically",
      "ratio -> 0.36):", ok(okk))

print("\n== (3.39) and Lemma 3.14 ==")
mp.dps = 25
l2 = mpf(LAMBDA2.mid().str(20, radius=False))
worst = mpf(1)
for i in range(1, 400):
    lam = l2 * i / 400
    I = quad(lambda x: 1 / (x ** 3 * mlog(x)), [lam, l2])
    bound = mpf('6.86') + mpf('0.75') / (lam ** 2 * mlog(lam))
    worst = min(worst, I - bound)
print("  min over lambda-grid in (0, lambda2] of [int_l^l2 dx/(x^3 log x) - (6.86 + 0.75/(l^2 log l))] =", mp.nstr(worst, 6), ok(worst > 0))
J = (LAMBDA2 ** -3 + (2 * SIGMA1 - 1 - LAMBDA2) ** -3) / 2
print("  J(lambda2)*0.71 =", fmt(J * arb('0.71'), 6), "< 15.4 (J = half-sum, as needed)", ok(J * arb('0.71') < arb('15.4')))
print("  combined log T coefficient: -22.8*6.86 + 15.4 =", fmt(arb('-22.8') * arb('6.86') + arb('15.4'), 6),
      "(thesis -140);  -22.8*0.75 = -17.1 (thesis -17.09: rounding in the wrong direction, compensated by -141 -> -140 only",
      "while lambda^2|log lambda| >= 0.0099; negligible because of the 0.2-vs-0.0754 margin below)")
# C2 max (3.47): thesis claims C2(lambda*(T),T)(loglog T)^4/(log T)^3 <= 1.2532 (max at log T = 912.82)
def C2(lam, LT):
    L2 = math.log(LT)
    return (-(140 + 17.09 / (lam ** 2 * math.log(lam))) * LT - 1.7 * (math.log(lam) / lam ** 3 + 48)
            + (lam ** -3 - 39) * (1.7 * L2 + 16))
best = (0, 0)
LT = 225.4
while LT < 1e7:
    lam = 2.248 * math.log(LT) ** 2 / LT
    v = C2(lam, LT) * math.log(LT) ** 4 / LT ** 3
    if v > best[0]: best = (v, LT)
    LT *= 1.001
print(f"  max of C2(lambda*(T),T) L2^4/L1^3 over log T in [225.4, 1e7] (float grid) = {best[0]:.5f} at log T = {best[1]:.2f}"
      f"   [thesis 1.2532 at 912.82]")
Cm1 = C_ford(arb(-1), lam4(LOG_H2) / ETA1)
v = arb('1.26') * Cm1 * (A1 + EPS) ** 2 * arb('1.013') ** 3
print("  1.26 C(-1,nu)(A1+eps)^2 1.013^3 =", fmt(v, 6), "< 0.2 :", ok(v < arb('0.2')), "; sum a_k*0.2 =", fmt(arb('0.2') * A_SUM, 5), "<= 0.71")

print("\n== Lemma 3.6 base case: |(z-1)zeta(z)| <= c_j |Q+z|^(1+mu_j) |log(Q+z)| for |Im z| <= 3, Q = 3 ==")
print("  (the printed argument 'c_j > 1/2 and |(s-1)zeta(s)| < Q' does not imply this: 0.5*3.5*log 3.5 = 2.19 < 3;")
print("   direct check on a grid of 601 heights per line instead)")
Q = acb(3)
for sig, cj, muj in [(arb('0.5'), arb('0.618'), arb(1) / 6)] + [(sigma_n(n), arb('1.546'), 1 / arb(2 ** n - 2)) for n in range(4, 9)]:
    worst = arb(10)
    for i in range(601):
        tt = arb(i) / 100 - 3
        z = acb(sig, tt)
        lhs = abs((z - 1) * z.zeta()) if abs(z - 1) > arb('1e-30') else arb(1)
        rhs = cj * abs(Q + z) ** (1 + muj) * abs((Q + z).log())
        r = rhs / lhs
        if r < worst: worst = r
    print(f"  sigma = {fmt(sig, 6)}: min ratio rhs/lhs on grid = {fmt(worst, 5)}  {ok(worst > 1)}")
