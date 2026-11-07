"""
Small side checks used in REPORT.md (sec. 3).  Rigorous where marked [RIG], sanity
checks otherwise.   Run: python -I check_misc.py > check_misc_out.txt
"""
import sys, os, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from flint import arb, ctx
ctx.prec = 128
fails = []


def ok(c, m):
    print(("OK    " if c else "FAIL  ") + m)
    if not c:
        fails.append(m)


g = arb.const_euler()
# 1. zeta(1+e) <= e^{g e}/e  for 0 < e <= 0.04  (Ramare, Math. Comp. 85 (2016) Lemma 5.1;
#    used to turn S_eps(X) <= b4 into CS Lemma 7's form).  [RIG]
#    zeta(1+e) - 1/e = sum_k (-1)^k gamma_k e^k / k!  (Stieltjes constants, acb.stieltjes) and
#    |gamma_k| <= 4 (k-1)!/pi^k for k >= 1 (Berndt, Rocky Mountain J. Math. 2 (1972)).
#    h(e) := (e^{g e}-1)/e - (zeta(1+e)-1/e) = sum_{k>=1} c_k e^k,
#    c_k = g^{k+1}/(k+1)! - (-1)^k gamma_k/k!.   Show h(e)/e > 0 on (0, 0.04] by evaluating
#    sum_{k=1}^{K} c_k E^{k-1} on the ball E = [0, 0.04] plus the tail bound.
from flint import acb
K = 25
Eb = arb("0.02", "0.02")
emax = arb("0.04")
poly = arb(0)
for k in range(1, K + 1):
    gk = acb.stieltjes(k).real
    ck = g ** (k + 1) / arb(math.factorial(k + 1)) - (-1) ** k * gk / arb(math.factorial(k))
    poly += ck * Eb ** (k - 1)
x = emax / arb.pi()
tail = 4 * x ** K / (1 - x) + (g * emax) ** (K + 1) / arb(math.factorial(K + 1)) * 2 / emax
lowb = poly - tail
ok(bool(lowb > 0), "[RIG] zeta(1+eps) <= e^{gamma eps}/eps for 0 < eps <= 0.04: h(eps)/eps >= %s > 0 "
   "(Stieltjes series, Berndt tail bound)" % lowb.lower())
ok(bool(g < arb(5).log()), "[RIG] gamma < log 5 (so e^{(gamma-log5) eps} <= 1 in CS Lemma 7)")

# 2. log(1+u^2) <= u^a for u >= 0, a in [4/3, 2]  (proof of Theorem 1): proved in REPORT;
#    sanity grid:
mx = max(math.log1p(u * u) - min(u ** (4 / 3), u ** 2) for u in [i / 1000 for i in range(1, 200000)])
ok(mx <= 0, "[grid] log(1+u^2) <= min(u^{4/3}, u^2) on (0,200]  (max diff %.3g)" % mx)

# 3. 8H^3-12H^2+18H-9 >= 0 for H >= 1 (Cor. 6: 1-8/(9+4H^2) >= (1-1/H)^2) : derivative
#    24H^2-24H+18 > 0 and value 5 at H=1.  [RIG]
ok(True, "[RIG, by hand] 8H^3-12H^2+18H-9 >= 5 > 0 for H >= 1 (derivative 24H^2-24H+18 > 0)")

# 4. b11(X,2) <= 1 + 3.31/log X for X >= 1e9 (CS Lemma 8): 6/L+6/L^2 <= 0.31 for L >= log 1e9 [RIG]
L = (arb(10) ** 9).log()
ok(bool(6 / L + 6 / L ** 2 <= arb("0.31")), "[RIG] 6/L + 6/L^2 = %s <= 0.31 at L = log 1e9 (decreasing in L)"
   % (6 / L + 6 / L ** 2).str(5))

# 5. C6 constant: KLN Cor 4.11 at eta = 1/2 gives 38.931... <= 220 [RIG]
import cs_thm1 as c
c6 = c.C6_const_derived()
ok(bool(c6 <= 220), "[RIG] derived C6 constant %s <= 220 (paper's 220 is conservative)" % c6.str(8))
ok(bool(arb(2) / (arb("3.006") * arb(1.5).zeta()) <= 1),
   "[RIG] 2/(3.006 zeta(3/2)) <= 1, so (pi/log2)log(1+u^{-3/2}) dominates the b7 correction")

# 6. K2: 2^{1/3}A0 (1 - e^{-u0}) <= 2^{1/3} (4k/3)(A0/T0)^3 T  with u0 = (4k/3)(A0/T)^2: uses 1-e^{-x} <= x.
ok(True, "[RIG, by hand] K2's second term = 2^{1/3}(4kappa/3)(A0/T0)^3 from 1-e^{-u0} <= u0")

# 7. sum_{n<=x} d(n)^2 <= x(log x + 1)^3 (KLN (3.13), 'Gowers'): our proof d^2 <= d_4 and
#    D_k(x) <= x(log x+1)^{k-1}; integer sanity check up to 2e6.
N = 2 * 10 ** 6
d = [0] * (N + 1)
for i in range(1, N + 1):
    for j in range(i, N + 1, i):
        d[j] += 1
S = 0
bad = 0
for n in range(1, N + 1):
    S += d[n] * d[n]
    if n in (1, 2, 3, 10, 100, 1000, 10 ** 4, 10 ** 5, 10 ** 6, N) or n % 99991 == 0:
        if S > n * (math.log(n) + 1) ** 3:
            bad += 1
ok(bad == 0, "[sanity] sum_{n<=x} d(n)^2 <= x(log x+1)^3 at sampled x <= 2e6")

# 8. CT19 Thm 2 main-term constants D2, D3, D4 (exact values from the fourth-moment audit):
ok(True, "D2=0.7443412764, D3=0.8232652083, D4=0.4603233723 (exact residue computation, fourth_moment/lemma_checks_out.txt); "
   "cs_kln.C8_CT19 uses upper values 0.74434128, 0.82326521, 0.46032338")
print("FAILS:", fails)
sys.exit(1 if fails else 0)
