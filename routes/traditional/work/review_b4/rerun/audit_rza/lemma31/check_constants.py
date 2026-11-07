# Rigorous (Arb / exact rational) checks of the numerical constants entering
# RZA Lemma 3.1 (= RZ23 Thm 1.7 with g_1 -> g_2), Part 1 (the |Delta| bound).
#
# Chain (real s = 1+eps, sigma_0 = 1/2+eps), see REPORT.md:
#  |Delta_q| <= (2^eps/log2) * X^-1 int_1^X |m_q|  +  (1 + 2^{1/2+eps}(1+eps 2^{eps-1} log2)) sqrt(q)/phi_{1/2}(q)/sqrt(X)
#  int_1^X |m_q| <= 1.03*H1*g_2 q^xi/phi_xi X/log X 1_{X>=1e12} + g_0 sqrt(q)/phi_{1/2} sqrt(8X)   (Lemma 5.4 with Lemma 2.5)
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as F
from flint import arb, ctx

ctx.prec = 200
ok_all = True
def check(name, cond):
    global ok_all
    ok_all = ok_all and bool(cond)
    print(('OK   ' if cond else 'FAIL ') + name)

H1 = F(10032, 10**6); H2 = F(296, 10**4)
log2 = arb(2).log()
xi = 1 - 1 / (12 * arb(10).log())
print('xi =', xi)

# 1. g_2 constant: 2.9506 >= H2/H1 and H1*2.9506 >= H2
print('H2/H1 =', float(H2 / H1))
check('2.9506 >= H2/H1', F(29506, 10**4) >= H2 / H1)
check('H1*g2(2)*2^xi/phi_xi(2) = H1*2.9506 >= 0.0296', H1 * F(29506, 10**4) >= H2)
# (RZ23's g_1 uses 1.4378: H1*1.4378 vs 0.0296)
print('   RZ23 g_1: H1*1.4378 =', float(H1 * F(14378, 10**4)), '< 0.0296 -> RZ23 Lemma 5.2 not justified at q=2 for X>=1e12')
# g_0(2): sqrt(2)*g_0(2)*sqrt2/phi_{1/2}(2) = sqrt(3)
g02 = arb(3).sqrt() * (arb(2).sqrt() - 1) / 2
val = arb(2).sqrt() * g02 * arb(2).sqrt() / (arb(2).sqrt() - 1)
check('sqrt2*g0(2)*sqrt2/(sqrt2-1) == sqrt3 (enclosure contains)', abs(val - arb(3).sqrt()) < arb('1e-50'))
check('g0 identity: sqrt3(sqrt2-1)/2 == (sqrt6-sqrt3)/2', abs(g02 - (arb(6).sqrt() - arb(3).sqrt()) / 2) < arb('1e-50'))

# 2. T(y) = (log y / y) * int_A^y dt/log t <= 1.03 for y >= A = 1e12 (RZ23 Lemma 5.3 + script)
#    T'(y) has the sign of k(y) = y - (log y - 1) L(y), L(y) = li(y) - li(A).
#    At any critical point T = log y/(log y - 1), decreasing in y.
#    Plan: (i) k > 0 on [A, Y1] (grid, monotone bounds) => T increasing there, T <= T(Y1).
#          (ii) any critical point is >= Y1 => its value <= log Y1/(log Y1 - 1).
#          (iii) T(y) -> 1 as y -> oo.  Hence sup T <= max(T(Y1), logY1/(logY1-1), 1).
A = arb(10)**12
liA = A.li()
def L(y): return y.li() - liA
Y1 = arb(12) * arb(10)**14
logY1 = Y1.log()
crit = logY1 / (logY1 - 1)
print('log Y1/(log Y1 - 1) =', crit)
# grid geometric ratio r
import math
# adaptive: on [y,y2]: k >= y - (log y2 - 1) L(y2)  (L, log increasing)
nbad = 0; npts = 0
stack = [(A, Y1)]
while stack:
    y, y2 = stack.pop()
    kl = y - (y2.log() - 1) * L(y2)
    if kl > 0:
        npts += 1
    elif (y2 - y) / y < arb('1e-9'):
        nbad += 1
    else:
        md = (y * y2).sqrt()
        stack.append((md, y2)); stack.append((y, md))
check('k(y) > 0 on [1e12, 1.2e15] (%d cells, %d unresolved)' % (npts, nbad), nbad == 0)
TY1 = logY1 / Y1 * L(Y1)
print('T(Y1) =', TY1)
check('T(Y1) <= 1.03', TY1 < arb('1.03'))
check('critical value bound log Y1/(log Y1-1) <= 1.03', crit < arb('1.03'))
# locate actual maximum for information
lo, hi = arb(10)**15, arb(2) * arb(10)**15
for _ in range(80):
    md = (lo + hi) / 2
    if (md - (md.log() - 1) * L(md)) > 0: lo = md
    else: hi = md
print('critical point y0 ~', lo.mid().str(10), ' T(y0) ~', (lo.log() / lo * L(lo)).str(10), '(RZ23: y0=1365396548134370.8, T<=1.03)')
check('1.03*H1 <= 0.010333', F(103, 100) * H1 <= F(10333, 10**6))

# 3. Constants in Theorem 1.7 Part 1
c1 = arb(10333) / 10**6 * 2 / log2
print('0.010333*2^eps/log2 at eps=1:', c1)
check('0.010333*2/log2 <= 0.03  (log term, eps<=1)', c1 < arb('0.03'))
check('sqrt8/log2 <= 4.09 <= 4.1', arb(8).sqrt() / log2 < arb('4.09'))
print('   sqrt8/log2 =', arb(8).sqrt() / log2)
check('1+sqrt2 <= 2.42', 1 + arb(2).sqrt() < arb('2.42'))
check('sqrt2*log2/2 <= 0.50', arb(2).sqrt() * log2 / 2 < arb('0.5'))
check('2.42 + 0.50 e2^e <= (5+e2^e)/2  (trivial: 2.42<=2.5)', True)
# 4. analytic inequalities used: for eps in (0,1]: 1/(c(1+e) zeta(1+e)) <= e 2^e/log2,
#    e(1+e) := 2^-e (1+2^{e-1} e log2) log2 >= (1-2^-e)/e   (real-s version of Lemma 6.4(ii))
bad = 0
for k in range(1, 2001):
    e = arb(k) / 2000
    c = (1 - arb(2)**(-e)) / e
    z = (1 + e).zeta()
    if not (1 / (c * z) <= e * arb(2)**e / log2): bad += 1
    ee = arb(2)**(-e) * (1 + arb(2)**(e - 1) * e * log2) * log2
    if not (ee >= c): bad += 1
    if not (e * z > 1): bad += 1
check('grid check (2000 pts) of 1/(c zeta) <= e2^e/log2, e(s) >= c(s), e*zeta(1+e) > 1', bad == 0)
print('ALL OK' if ok_all else 'SOME CHECK FAILED')
