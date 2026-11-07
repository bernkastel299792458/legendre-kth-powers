# float brute-force check of Lemma D: S_abs = sum_{v<=V,w<=W} |psi_v||theta_w| [v,w]^{-1/2}  <=  bound
import sys, math, numpy as np
sys.path.insert(0, '..'); sys.path.insert(0, '.')
from lemmaD_mollifier import S_abs_bound, f_up, _mobius
from math import gcd
for (U, V, W) in ((10, 300, 20), (30, 3000, 50), (50, 5000, 200), (100, 20000, 100), (5, 20000, 400)):
    mu, _ = _mobius(int(V))
    D = math.log(V / U); lW = math.log(W)
    vs = [v for v in range(1, int(V) + 1) if mu[v] != 0]
    ws = [w for w in range(1, int(W) + 1) if mu[w] != 0]
    psi = np.array([min(1.0, math.log(V / v) / D) for v in vs]); vv = np.array(vs, dtype=float)
    S = 0.0
    for w in ws:
        th = math.log(W / w) / lW
        if th <= 0: continue
        g = np.gcd(np.array(vs), w).astype(float)
        S += th * np.sum(psi * (vv * w / g) ** -0.5)
    b = f_up(S_abs_bound(U, V, W))
    print(f"U={U} V={V} W={W}:  S_abs={S:.5f}  bound={b:.5f}  ratio={b/S:.3f}   S/sqrt(VW)={S/math.sqrt(V*W):.5f}")
