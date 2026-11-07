"""
explore_repair.py -- EXPLORATION ONLY (not a proof).  What a corrected version of RZA's chain
might give.  Exact identity (checked numerically in rza_counterexample.py):
   S_eps(X) = sum_l w_l (m_l(X/l) + eps Delta_l(X/l,eps))^2 + 2/zeta - G(X)/zeta^2,
   w_l = mu^2 phi_{1+eps}(l) X^{-2eps}/l^2 = X^{-eps} b_l c_eps(l) (l/X)^eps,
   b_l = mu^2 phi(l)/l^2,  c_eps(l) = prod_{p|l} (1 + (1-p^{-eps})/(p-1)).
So the main term decays like X^{-eps} (paper: X^{-2eps}).  Heuristic model: re-use the audited
constants of rza_audited.py, put X^{-eps} where the paper had X^{-2eps}, a factor 10.9^{-eps}
for the l <= X/10.9 terms, and inflate every l-sum by kappa(eps) = exp(lam*eps) (c_eps(l) <= exp(eps sum_{p|l} log p/(p-1));
lam is NOT computed rigorously here; we show lam = 2, 4, 6, 10).  Maximise over eps in [0, eps0] on a
fine grid at X = T (worst case).
"""
import os, sys, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rza_audited import build
from rza_common import EG
inp, o, th, status, Kc = build(False)
f = lambda x: float(x.mid())
Kb, Kc_, Ka, D0, D1, D2, D3 = map(f, (o["K_b"], o["K_c"], o["K_a"], o["D0"], o["D1"], o["D2"], o["D3"]))
uc1 = f(o["uc1"]); L0 = 12 * math.log(10); KL = 0.03 * uc1 / (1 + L0); g = float(EG.mid())
def F(eps, X, Theta, kappa):
    lX = math.log(X)
    xe = X ** (-eps); s = 10.9 ** (-eps)
    main = xe * kappa * Theta
    cross = 2 * eps * xe * kappa * (0.03 * uc1 * (1 + max(0, math.log(lX / L0))) + s * (Kb * 2 ** eps + Kc_ * eps * 4 ** eps)) \
        + 2 * eps * xe * Ka
    sq = eps ** 2 * xe * s * kappa * (D0 + D1 * 4 ** eps + D2 * eps * 8 ** eps + D3 * eps ** 2 * 16 ** eps)
    zg = 2 * eps - 9.1 * eps ** 2 * math.exp(-2 * g * eps)
    return main + KL + cross + sq + zg
def F2(eps, X, Theta, lam):
    return F(eps, X, Theta, math.exp(lam * eps))      # c_eps(l) <= exp(eps * sum_{p|l} log p/(p-1)); lam models that sum
for (lab, T, Theta) in [("X>=1e12", 1e12, f(th[("1e12", "1e16")][1])), ("X>=3e12", 3e12, f(th[("3e12", "1e16")][1]))]:
    for eps0 in (1 / 25, 1 / 44):
        row = []
        for lam in (2.0, 4.0, 6.0, 10.0):
            best = max((F2(k * eps0 / 4000, T, Theta, lam), k * eps0 / 4000) for k in range(4001))
            row.append("lam=%.0f: sup=%.4f at eps=%.4f" % (lam, best[0], best[1]))
        print("%s eps<=1/%d  Theta=%.4f | %s" % (lab, round(1 / eps0), Theta, " | ".join(row)))
