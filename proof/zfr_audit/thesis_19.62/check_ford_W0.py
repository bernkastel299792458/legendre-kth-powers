"""Independent check of Ford's bound (thesis Lemma 2.3 = BTY Lemma 4):
    |W0(z)| = |W(z) - w(0)/z| <= C(nu, r)|z|^-3   for Re z >= nu, |z| >= r,
at theta = 1.1272 (thesis Ch. 3) and theta = 1.1338 (thesis Ch. 2 / BTY).

* W(z) = int_0^{2 th cot th} e^{-zu} w(u) du is computed with arb (acb.integral)
  from the explicit w(u) of Definition 3.1;
* w(u) is compared with Ford's definition w = g*g, g(u) = (cos(u tan th) - cos th) sec^2 th;
* |z|^3 |W0(z)| -> |w''(0)| = sec(th) * c0_printed * c3, so the printed constant
  c0 = csc th sec^2 th cannot be right; Ford has c0 = csc th sec^3 th.

Run:  python -I check_ford_W0.py > check_ford_W0_output.txt
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import *

def W(z, theta):
    d = 2 * theta * cot(theta)
    f = lambda u, an: (-acb(z) * u).exp() * w_acb(u, theta)
    return acb.integral(f, 0, acb(d))

def g_ford(x, theta):
    return ((x * acb(tan(theta))).cos() - acb(theta.cos())) * acb(sec(theta) ** 2)

for th in ['1.1272', '1.1338']:
    theta = arb(th)
    W0 = w0(theta)
    b = theta / tan(theta)
    print(f"theta = {th}:  w(0) = {fmt(W0, 10)}")
    for u in ['0', '0.3', '0.7', '1.0']:
        u = arb(u)
        lo, hi = (u - b).max(-b), b
        conv = acb.integral(lambda x, an: g_ford(x, theta) * g_ford(acb(u) - x, theta), acb(lo), acb(hi)).real
        print(f"   w({fmt(u,3)}): Definition 3.1 = {fmt(w(u, theta), 12)},  Ford g*g = {fmt(conv, 12)}")
    t = tan(theta)
    w2 = sec(theta) ** 2 * (t ** 2 - theta * t * sec(theta) ** 2)
    print(f"   w''(0) = {fmt(w2, 10)};  lim |z|^3|W0| = |w''(0)| = {fmt(abs(w2), 8)}")
    print(f"   C(nu, infinity) with printed c0 = {fmt(C_ford(arb(0), arb(10)**12, theta, printed=True), 8)}"
          f"  (< |w''(0)|: printed formula impossible);  with Ford's c0 = {fmt(C_ford(arb(0), arb(10)**12, theta), 8)}")
    tests = [(-1, 76.36), (0, 76.36), (-1, 138), (138, 138), (0, 1000), (-1, 10000), (5, 300)]
    for nu, r in tests:
        nu, r = arb(nu), arb(r)
        Cp = C_ford(nu, r, theta, printed=True); C = C_ford(nu, r, theta)
        y = (r ** 2 - nu ** 2).sqrt() if r > abs(nu) else arb(0)
        z = acb(nu, y)
        ratio = abs(W(z, theta) - acb(W0) / z) * abs(z) ** 3
        print(f"   z = {fmt(nu,4):>7s} + {fmt(y,8):>10s} i:  |W0||z|^3 = {fmt(ratio, 7)}   printed C = {fmt(Cp, 7)}"
              f" {'(violated)' if ratio > Cp else ''}   Ford C = {fmt(C, 7)} {'OK' if ratio < C else '** EXCEEDS **'}")
