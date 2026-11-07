# -*- coding: utf-8 -*-
"""
Sensitivity of Corollary 4's a1(A0), a2(A0) at log10 A0 = 11.46 and of the parent's final constant,
which depends on a_j only through a_j^{1/3} raised to an exponent <= 3(1-s)/(2-s) <= 0.091 (s >= 0.96875).
Run: python -I sensitivity.py > sensitivity_out.txt
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from recursion import a12, QE
from cs4_formulas import Q, arb, PI, ctx

ctx.prec = 128
A0 = arb(10) ** Q("11.46")
EXP = 3 * (1 - Q("0.96875")) / (2 - Q("0.96875"))
print("exponent 3(1-s)/(2-s) at s=0.96875: %s" % EXP.str(6))
base1, base2 = a12(A0, Q("34.842"), QE("1.3897e16"), QE("9.5079e15"))
print("paper constants: a1 = %s  a2 = %s" % (base1.str(10), base2.str(10)))
cases = [
    ("corrected chain (CHT21 +0.73x^1/2 term)", Q("34.842"), QE("1.38962e16"), QE("9.50787e15")),
    ("M1(1e10) + 1.0", Q("35.842"), QE("1.3897e16"), QE("9.5079e15")),
    ("M1(1e10) x 1.5", Q("52.263"), QE("1.3897e16"), QE("9.5079e15")),
    ("frakM2, M2(1e10,2e10) x 2", Q("34.842"), QE("2.7794e16"), QE("1.90158e16")),
    ("everything x 2 (M1, frakM2, M2(1e10,2e10))", Q("69.684"), QE("2.7794e16"), QE("1.90158e16")),
]
print("%-48s %-14s %-14s %-12s %-12s %-12s" % ("case", "a1", "a2", "a1/a1p", "a2/a2p", "(a2/a2p)^(EXP/3)"))
for lab, m1, f2, u in cases:
    a1, a2 = a12(A0, m1, f2, u)
    r1 = a1 / base1
    r2 = a2 / base2
    eff = (EXP / 3 * r2.log()).exp()
    print("%-48s %-14s %-14s %-12s %-12s %-12s" % (lab, a1.str(6), a2.str(6), r1.str(6), r2.str(6), eff.str(6)))
# what a factor-2 error in a2 does to the final constant (exponent EXP applied to a2^{1/3})
for f in (Q("1.01"), Q("1.1"), Q("2"), Q("10")):
    print("a2 multiplied by %s -> final-constant factor (a2^{1/3})^EXP = %s" % (f.str(4), (EXP / 3 * f.log()).exp().str(6)))
# heuristic size of the truth: M2(A0) ~ int_0^A0 P2(log(t/2pi)) dt (CFKRS (5.1.5)), non-rigorous float
import math
P2C = [1.312424385961669, 3.227907964901255, 2.425962198846682, 0.69886988487898, 0.0506605918211689]
X = float(A0.mid()) / (2 * math.pi)
l = math.log(X)
tot = sum(ck * X * sum((-1) ** (k - j) * math.factorial(k) / math.factorial(j) * l ** j for j in range(k + 1))
          for k, ck in enumerate(P2C)) * 2 * math.pi
print("[NON-RIGOROUS] Heath-Brown/CFKRS asymptotic M2(A0) ~ %.4e  vs a1(A0) = %.4e  (ratio %.1f)"
      % (tot, float(base1.mid()), float(base1.mid()) / tot))
