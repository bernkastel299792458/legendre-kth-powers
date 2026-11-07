"""Small numbers quoted in REVIEW.md: VK crossover of the top band, minimum mu_low over band-end cells (code path)."""
import os, sys, json, math
SRC = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'phase1_littlewood'))
sys.path.insert(0, SRC)
from mpmath import mp, mpf, findroot
from zl_core import *
import cert_profile as CP
import cert_v2 as C2

mp.dps = 30
zvk = lambda v: mpf('54.004') * mp.log(v) ** (mpf(4) / 3) / v ** (mpf(1) / 3)
vx = findroot(lambda v: zvk(v) - mpf('11.691'), mpf(5.8e6))
print("Z_VK(v) = 11.691 at v =", mp.nstr(vx, 8))
vx2 = findroot(lambda v: mpf('5.558691') * mp.log(v) - mpf('18.919'), mpf(30))
print("5.558691 log v = 18.919 at v =", mp.nstr(vx2, 8))
d = json.load(open(os.path.join(SRC, 'profile_v2.json')))
prof = [[float(a), float(b), str(Z)] for a, b, Z, ln in d['bands']]
zw, above = C2.make_zw(float(d['V1']))
mus = []
for i, (a, b, Z) in enumerate(prof):
    for va in (a, b - 1e-6 * max(1, b / 100)):
        vb = va + 1e-6 * max(1, va / 100)
        Zw = zw(prof, va, vb, float(d['V0']), float(d['V1']))
        Zwa = Zw if Zw > arb(Z) else arb(Z)
        r = cell_terms(arb(va), arb(vb), arb(Z), Zwa, (d['bands'][i][3])[0])
        if r is not None:
            mus.append((float(r[0].lower()), i, va))
mus.sort()
print("smallest mu_low at band-end cells:", mus[:3])
