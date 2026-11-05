"""Main-term estimates of thesis Ch. 3: Lemma 3.6 (zeta bounds), Lemma 3.8
(H1 <= t <= H2) and Lemma 3.9 (t >= H2), each claiming

    (1/4 lambda*) sum_k a_k int [log|zeta(s_k - lambda* + iu delta)| - log|zeta(s_k + lambda* + iu delta)|] /cosh^2 u du
        <= 3.4431 log t / loglog t.

We compute the coefficient c(t) of log t/loglog t produced by the thesis's own
ingredients (Lemma 3.6 + Lemma 3.7 + (3.19) + (3.20)) with no intermediate
rounding:

  c(t) = L2/L1 * [ sum_k a_k (mu(s) log T_k + loglog T_k + log C(s)) + a0 (g x - log x) ] / (2 lambda*),
  s = sigma* - lambda*,  x = sigma* + lambda* - 1,  T_k = k t,

with A = A1 (worst case: c increases with A).  Choices that favour the thesis are
made throughout (thesis C_3 although it is marginally too small, sigma* instead of
sigma1 in the zeta(sigma*+lambda*) term).

Run:  python -I check_main_term.py > check_main_term_output.txt   (about 1-2 min)
"""
import os, sys, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import *

LOG_K = [arb(k).log() for k in range(K + 1)]


def coef_direct(L1, lam, n, A=A1):
    """Coefficient c(t) for given log t (ball ok), lambda, and Lemma 3.6 index n."""
    L2 = L1.log()
    s = sigma_star(L1, A)
    sl = s - lam
    mu = mu_n(n, sl)
    logC = C3_thesis(sl).log() if n == 3 else arb('1.549').log()
    tot = arb(0)
    for k in range(1, K + 1):
        T = L1 + LOG_K[k]
        tot += A_K[k] * (mu * T + T.log() + logC)
    tot += A_K[0] * logzeta_upper(s + lam - 1)
    return tot / (2 * lam) * L2 / L1


def n_range(sl):
    """indices n with sigma_n <= sl <= sigma_{n+1} possible (ball-aware)."""
    res = []
    for n in range(3, 200):
        lo, hi = sigma_n(n), sigma_n(n + 1)
        if sl.upper() >= lo.lower() and sl.lower() <= hi.upper():
            res.append(n)
        if lo.lower() > sl.upper():
            break
    return res


def coef_cell(L1, lam_fun):
    lam = lam_fun(L1)
    sl = sigma_star(L1) - lam
    ns = n_range(sl)
    if not ns or sl.lower() < arb('0.5').upper():
        return None, ns
    vals = [coef_direct(L1, lam, n) for n in ns]
    m = vals[0]
    for v in vals[1:]:
        m = m.max(v) if hasattr(m, 'max') else (v if v > m else m)
    return m, ns


def ball(a, b):
    a, b = arb(a), arb(b)
    return arb((a + b) / 2, (b - a) / 2)


print("== 1. Lemma 3.6 constants ==")
eps2 = (PI / (LOG_H1 - arb(2).log())) ** 2
print("eps2 = (pi/log(H1/2))^2 =", fmt(eps2), "  [thesis: < 2.5e-3]  ", "OK" if eps2 < arb('2.5e-3') else "** FALSE **")
fac = (1 + eps2) ** arb('0.5')
for sig, cj in [(arb('0.5'), arb('0.618')), (arb(5) / 7, arb('1.546'))]:
    need = cj * fac
    have = C3_thesis(sig)
    print(f"  sigma={fmt(sig,6)}: true constant >= {fmt(need)}  thesis C3 = {fmt(have)}  ",
          "OK" if have >= need else "too small (by %s relative)" % fmt(need / have - 1, 3))
print("  n>=4: 1.546*(1+eps2)^(1/2) =", fmt(arb('1.546') * fac), "<= 1.549 :", arb('1.546') * fac < arb('1.549'))
print("  (effect of the C3 shortfall on c(t) is < 1e-4; ignored below, i.e. thesis C3 is used)")

print("\n== 2. Domain of Lemma 3.6/3.7: sigma*-lambda* must lie in [sigma_n, sigma_{n+1}] (and >= 1/2) ==")
for Lx in ['56.5', '56.8', '57.0', '57.1']:
    L = arb(Lx)
    print(f"  log t = {Lx:6s}: sigma*-lambda*(n=3 formula) = {fmt(sigma_star(L) - lam3(L), 8)}  (needs >= 0.5)")
for Lx in ['216', '217', '217.4', '217.5']:
    L = arb(Lx)
    print(f"  log t = {Lx:6s}: sigma*-lambda*(n=4 formula) = {fmt(sigma_star(L) - lam4(L), 8)}  (needs >= 5/7 = 0.71428571)")

print("\n== 3. Thesis's reduced bound (3.21): (1.7761 d_n E_n + 0.0244) + E(t) L2/L1 ==")
def E_thesis(L1, n):
    lam = lam3(L1) if n == 3 else lam4(L1)
    L2 = L1.log()
    if n == 3:
        return (arb('3.53') * L2 - (lam - arb('0.004')).log() + arb('1.73')) / (2 * lam) - arb('7.24')
    return (arb('3.53') * L2 - (lam - arb('0.004')).log() + arb('3.28')) / (2 * lam) + GAMMA / 2
def E_correct(L1, n):
    """same reduction, but with 3.53*log C_n carried out correctly."""
    lam = lam3(L1) if n == 3 else lam4(L1)
    L2 = L1.log()
    if n == 3:   # 3.53 (L2 + 1.66 - 4.27 lam) + 0.07 - log(lam - 0.004), over 2 lam, + g/2
        return (arb('3.53') * (L2 + arb('1.66')) + arb('0.07') - (lam - arb('0.004')).log()) / (2 * lam) \
               - arb('3.53') * arb('4.27') / 2 + GAMMA / 2
    return (arb('3.53') * (L2 + arb('1.549').log()) + arb('0.07') - (lam - arb('0.004')).log()) / (2 * lam) + GAMMA / 2
for n, lo, hi, step in [(3, 56.5, 216, 0.01), (4, 216, 225.4, 0.01)]:
    best_t = (arb(-99), 0); best_c = (arb(-99), 0)
    x = lo
    while x <= hi + 1e-9:
        L = arb(repr(round(x, 4)))
        vt = E_thesis(L, n) * L.log() / L
        vc = E_correct(L, n) * L.log() / L
        if vt > best_t[0]: best_t = (vt, x)
        if vc > best_c[0]: best_c = (vc, x)
        x += step
    En = E3 if n == 3 else E4
    head = arb('1.7761') * delta_n(n) * En + arb('0.0244')
    print(f"  n={n}: max E_thesis L2/L1 = {fmt(best_t[0],6)} at log t = {best_t[1]:.2f}"
          f"  [thesis: {'0.87153 near 111.12' if n==3 else '1.0319 near 222.75'}];  total = {fmt(head + best_t[0],6)}")
    print(f"        max E_correct L2/L1 = {fmt(best_c[0],6)} at log t = {best_c[1]:.2f};  total = {fmt(head + best_c[0],6)}"
          f"  {'> 3.4431 !!' if head + best_c[0] > arb('3.4431') else '<= 3.4431'}")

print("\n== 4. Direct coefficient c(t), thesis lambda*, A = A1 (no rounding) ==")
pts = ['56.5', '60', '70', '80', '90', '95.5', '100', '111.12', '130', '150', '160', '170', '200', '216']
for p in pts:
    L = arb(p)
    v = coef_direct(L, lam3(L), 3)
    print(f"  log t = {p:7s}: c = {fmt(v, 8)}")
for p in ['216', '217', '220', '222.75', '225.4']:
    L = arb(p)
    sl = sigma_star(L) - lam4(L)
    n = 3 if sl < arb(5) / 7 else 4
    print(f"  log t = {p:7s}: c = {fmt(coef_direct(L, lam4(L), n), 8)}  (n = {n} data, since sigma*-lambda* = {fmt(sl, 7)})")
Lw = arb('95.5')
cw = coef_direct(Lw, lam3(Lw), 3)
print(f"  RIGOROUS POINT CHECK: at log t = 95.5, c = {cw.str(15)}  (lower end {cw.lower().str(10)})")
print("    > 3.4431 (claimed):", cw > arb('3.4431'), ";  > 3.4465 (largest value the final slack can absorb):", cw > arb('3.4465'))

print("\n   rigorous cell scan of c(t) over [56.5, 225.4] (cells of width 1/8 in log t):")
cells_bad = []
cmax = arb(0); Lmax = None
x = 56.5
while x < 225.4 - 1e-12:
    y = min(x + 0.125, 225.4)
    Lb = ball(repr(x), repr(y))
    lf = lam3 if y <= 216 else lam4
    if x < 216 < y:
        lf = None
    if lf is None:
        v1, _ = coef_cell(ball(repr(x), '216'), lam3); v2, _ = coef_cell(ball('216', repr(y)), lam4)
        v = v1.max(v2) if (v1 is not None and v2 is not None) else None
    else:
        v, ns = coef_cell(Lb, lf)
    if v is None:
        cells_bad.append((x, y))
    else:
        if v.upper() > cmax.upper(): cmax = arb(v.upper()); Lmax = (x, y)
    x = y
print(f"   sup over cells (upper bound) = {fmt(cmax, 8)} on cell {Lmax}")
print(f"   cells where Lemma 3.6 does not apply (sigma*-lambda* < 1/2): {cells_bad[:3]}{' ...' if len(cells_bad)>3 else ''}  count={len(cells_bad)}")
# range where c > 3.4431 (float scan of point values)
lo_bad = hi_bad = None
x = 56.5
while x <= 216:
    L = arb(repr(round(x, 3)))
    if coef_direct(L, lam3(L), 3) > arb('3.4431'):
        if lo_bad is None: lo_bad = x
        hi_bad = x
    x += 0.1
print(f"   c(t) > 3.4431 for log t in about [{lo_bad:.1f}, {hi_bad:.1f}] (thesis lambda*)")

print("\n== 5. Best possible lambda per t (same ingredients; lambda in (0.2779, 0.5), sigma*-lambda >= 1/2) ==")
def best_lambda(Lx):
    L = arb(Lx)
    s = sigma_star(L)
    best = None
    for i in range(2780, 5000, 2):
        lam = arb(i) / 10000
        sl = s - lam
        if sl < arb('0.5'):
            continue
        n = 3 if sl <= arb(5) / 7 else (4 if sl <= arb(5) / 6 else None)
        if n is None: continue
        v = coef_direct(L, lam, n)
        if best is None or v < best[0]: best = (v, float(lam.mid()))
    return best
sup = (arb(0), None)
for Lx in [str(v) for v in range(57, 217, 3)]:
    b = best_lambda(Lx)
    if b[0] > sup[0]: sup = (b[0], Lx, b[1])
print(f"   sup_t min_lambda c(t, lambda) ~= {fmt(sup[0], 6)} at log t = {sup[1]} (lambda = {sup[2]:.4f})  [grid; indicative]")
for Lx in ['60', '100', '120', '126', '129', '132', '140', '200']:
    b = best_lambda(Lx)
    print(f"     log t = {Lx:4s}: min_lambda c = {fmt(b[0], 6)} at lambda = {b[1]:.4f}")

print("\n== 6. Lemma 3.9 (t >= H2): direct coefficient with the (1 - sigma*) term the thesis drops ==")
def coefH_cell(Lb):
    lam = lamH(Lb)
    sl = sigma_star(Lb) - lam
    ns = n_range(sl)
    vals = []
    for n in ns:
        L2 = Lb.log()
        mu = mu_n(n, sl)
        logC = C3_thesis(sl).log() if n == 3 else arb('1.549').log()
        tot = arb(0)
        for k in range(1, K + 1):
            T = Lb + LOG_K[k]
            tot += A_K[k] * (mu * T + T.log() + logC)
        h = (B * L2 ** 2 - A1 * L2) / Lb      # (3.25): sigma*+lambda*-1 >= h(t)
        tot += A_K[0] * logzeta_upper(h)
        vals.append(tot / (2 * lam) * L2 / Lb)
    m = vals[0]
    for v in vals[1:]: m = m.max(v)
    return m
cmaxH = arb(0); where = None
x = arb('225.4')
r = arb('1.0005')
while x < arb(10) ** 7:
    y = x * r
    v = coefH_cell(arb((x + y) / 2, (y - x) / 2))
    if v.upper() > cmaxH.upper(): cmaxH = arb(v.upper()); where = float(x.mid())
    x = y
print(f"   sup over log t in [225.4, 1e7] (rigorous cells, ratio 1.0005) = {fmt(cmaxH, 8)} near log t = {where:.1f}",
      "<= 3.4431 OK" if cmaxH < arb('3.4431') else "> 3.4431")
