"""For k in [65, 85]: HYB threshold vs Lee's xA/xB and the lower-side ceiling."""
from bound import delta, chl_ceiling
from math import inf
LEE = {85: (6162, 5587), 84: (6828, 5587), 83: (7546, 5587), 82: (8450, 5587), 81: (9685, 5588),
       80: (10986, 5588), 79: (12799, 5588), 78: (15286, 5589), 77: (18427, 5592), 76: (23736, 5601),
       75: (29735, 5880), 74: (43186, 6561), 73: (58051, 7554), 72: (96051, 9036), 71: (212515, 11620),
       70: (580009, 15951), 69: (2133517, 23148), 68: (12318302, 43001), 67: (37420887, 238050),
       66: (39361821, None), 65: (41432145, None)}

def best_any(L, k):
    b = inf
    for mode, ss in (('HYB', (0.985, 0.99)), ('KLN', (0.985,))):
        for s in ss:
            cs = [1 + i * 4e-3 for i in range(1, 150)]
            for step in (4e-3, 4e-4, 4e-5):
                d, c = min((delta(L, c / k, k, mode=mode, sstar=s), c) for c in cs)
                b = min(b, d)
                cs = [c + j * step / 10 for j in range(-10, 11) if c + j * step / 10 > 1]
    return b

print(" k  lower_ceiling  Lee_best   HYB_threshold(grid 25, scanning down from 3e5)")
for k in range(85, 64, -1):
    # find smallest L on a grid such that delta<1 for all grid points above (up to 3e5)
    L = 300000
    step = 1000
    thr = None
    Ls = list(range(300000, 20000, -2000)) + list(range(20000, 2000, -25))
    for L in Ls:
        if best_any(L, k) < 1:
            thr = L
        else:
            break
    lee = min(v for v in LEE[k] if v)
    print(f"{k:2d}  {chl_ceiling(k):11.1f}  {lee:9d}  {thr}", flush=True)
