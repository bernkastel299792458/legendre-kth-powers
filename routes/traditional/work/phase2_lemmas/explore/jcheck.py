# float sanity check (not rigorous): -J(r1) for s = 1+r+it vs TZ's BTZ and the Weyl version BTZW
import sys, math, mpmath as mp
sys.path.insert(0, '..')
from lemmaB_weyl import BTZW
from lemmaB_count import BTZ
from flint import arb
mp.mp.dps = 15
def J(r, t, r1):
    s = mp.mpc(1 + r, t)
    f = lambda th: mp.cos(th) * mp.log(abs((s + r1 * mp.expj(th) - 1) / (s + r1 * mp.expj(th) + 1) * mp.zeta(s + r1 * mp.expj(th))))
    return mp.quad(f, mp.linspace(0, 2 * mp.pi, 41)) / (mp.pi * r1)
for t in (1000.0, 5000.0, 20000.0):
    for r in (0.02, 0.05):
        r1 = 0.5 + r - 1e-4
        mJ = -J(r, t, r1)
        print(f"t={t} r={r}: -J={float(mJ):.4f}   BTZ={float(BTZ(arb(r), arb(math.log(t))).upper()):.4f}   BTZW={float(BTZW(arb(r), arb(math.log(t))).upper()):.4f}", flush=True)
