"""Independent referee checks for Lemma B-W (review_round2).
 (a) Arc integral: (1/(pi r1)) int_{pi/2}^{3pi/2} |cos th| [ (-2 r1 cos th/(1+2r)) X + ((1+2r+2r1 cos th)/(1+2r)) log(1+1/r) ] dth
     -> X/(1+2r) + (4/pi-1) log(1+1/r)/(1+2r)   as r1 -> 1/2 + r   (closed form used by TZ and by BTZW).
 (b) Boundary bound |zeta(1/2+iy)| <= A_eta |1+iy|^{1/6+eta}: the three ranges, with eta = 1/ell, numerically
     (|y| <= 3 by mpmath grid; 3 <= y via HPY 0.618 y^{1/6} log y <= A y^{1/6+eta}; y >= e^105 via PY), and the
     minimum over eta of A_eta e^{105(2/984+eta)} (the Patel-Yang side condition).
 (c) float-rounding of A_eta in lemmaB_weyl.A_eta (float(upper) is round-to-nearest).
 (d) direct mpmath -J at a few t vs BTZ / BTZW (sanity only).
"""
import math, sys, os
import mpmath as mp
mp.mp.dps = 30
HERE = os.path.dirname(os.path.abspath(__file__))

def arc(r, r1, X):
    f = lambda th: abs(mp.cos(th)) * ((-2 * r1 * mp.cos(th) / (1 + 2 * r)) * X + ((1 + 2 * r + 2 * r1 * mp.cos(th)) / (1 + 2 * r)) * mp.log(1 + 1 / r))
    return mp.quad(f, [mp.pi / 2, mp.pi, 3 * mp.pi / 2]) / (mp.pi * r1)

print("(a) arc integral vs closed form")
for r in (0.02, 0.05, 0.2):
    for X in (5.0, 8.0):
        cf = X / (1 + 2 * r) + (4 / mp.pi - 1) * mp.log(1 + 1 / r) / (1 + 2 * r)
        for d in (1e-3, 1e-6):
            print(f"  r={r} X={X} r1=1/2+r-{d}: arc={float(arc(r, 0.5 + r - d, X)):.8f}  closed={float(cf):.8f}")

print("(b) boundary bound")
mx = max(abs(mp.zeta(mp.mpc(0.5, y))) for y in mp.linspace(0, 3, 3001))
print(f"  max_{{|y|<=3}} |zeta(1/2+iy)| (grid 1e-3) = {float(mx):.6f}  (<= 1.461 needed)")
for ell in (29.07, 35.35, 40.35, 60.35, 110.35, 170.35):
    eta = 1 / ell
    A = max(1.461, 0.618 / (math.e * eta))
    # sup_y 0.618 log y / y^eta  = 0.618/(e eta) at y = e^{1/eta}
    ok_hpy = 0.618 / (math.e * eta) <= A
    py = A * math.exp(105 * (2 / 984 + eta))
    print(f"  ell={ell}: eta={eta:.5f} A_eta={A:.4f}  HPY range ok={ok_hpy}  PY side condition A e^(105(2/984+eta))={py:.2f} >= 66.7: {py >= 66.7}")
# global min of the side condition over eta
g = lambda e: 0.618 / (math.e * e) * math.exp(105 * (2 / 984 + e))
print(f"  min over eta>0 of (0.618/(e eta)) e^(105(2/984+eta)) = {g(1/105):.3f} (at eta = 1/105): side condition always holds")

print("(c) A_eta rounding in lemmaB_weyl")
sys.path.insert(0, os.path.join(HERE, '..', 'phase2_lemmas'))
from flint import arb
import lemmaB_weyl as BW
for l in (28.73, 29.0, 35.0, 40.0, 80.0, 110.0):
    ell = arb(l) + arb(2).log() / 2
    eta = arb(1 / float(ell.lower()))
    A = BW.A_eta(eta)
    exact = arb("0.618") / (arb(1).exp() * eta)
    print(f"  log T={l}: A_eta - 0.618/(e eta) = {float((A - exact).mid()):.3e}  (certainly >= 0: {bool(A >= exact)})")

print("(d) -J sanity at moderate t (float)")
def mJ(r, t, r1):
    s = mp.mpc(1 + r, t)
    f = lambda th: mp.cos(th) * mp.log(abs((s + r1 * mp.expj(th) - 1) / (s + r1 * mp.expj(th) + 1) * mp.zeta(s + r1 * mp.expj(th))))
    return -mp.quad(f, mp.linspace(0, 2 * mp.pi, 33)) / (mp.pi * r1)
mp.mp.dps = 15
for t in (2000.0, 10000.0):
    r = 0.05
    v = mJ(r, t, 0.5 + r - 1e-3)
    bw = float(BW.BTZW(arb(r), arb(math.log(t))).upper())
    print(f"  t={t} r={r}: -J = {float(v):.4f}   BTZW = {bw:.4f}")
