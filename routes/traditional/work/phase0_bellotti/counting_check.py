"""Float sanity check (not part of any rigorous claim) of the counting step in Bellotti §4.

Boxes ((m-1)h, m h], one representative per box (here: every box non-empty, worst case).
Per-pair weight (units 1/delta): w(D) = min(1/2, 1/(D/delta)) for D<1  [|Gamma(z)| X^{Re z} <= X^{2delta} min(1/(2delta),1/D)],
far pairs D>=1 are ignored here (they are the small c4 part).
Bellotti's claimed per-r bound (h = delta): 1/2 + sum_{n=1}^{1/delta-1} 1/n.
Our bound (h = lam*delta, K = 1): K/2 + sum_j P_j, see REPORT.md.
"""
import random, math
def per_r_sum(gam, r, delta):
    s = 0.0
    for g in gam:
        D = abs(g - gam[r])
        if D >= 1: continue
        s += min(0.5, delta / D) if D > 0 else 0.5
    return s
def our_bound(lam, delta, K=1.0):
    m = lambda d: K/2 if d <= 0 else min(K/2, 1/(lam*d))
    J1 = math.ceil(1/(lam*delta))
    tot = K/2
    dstar = 2/(K*lam); j0 = 1
    if dstar <= 0.5:
        tot += K/2 + 1/(lam*(1-dstar)); j0 = 2
    for j in range(j0, J1+1):
        if j-1 >= 2/(K*lam): tot += m(j-1) + m(j)
        else: tot += m(j-1) + m(j-0.5)
    return tot
def bellotti_bound(delta):
    return 0.5 + sum(1/n for n in range(1, int(1/delta)))
random.seed(1)
for delta in (0.0073, 0.015):
    for lam in (1.0, 2.0, 6.0):
        h = lam*delta
        nb = int(3/h) + 3
        worst = 0.0
        for trial in range(400):
            mode = trial % 4
            gam = []
            for m in range(1, nb+1):
                if mode == 0: th = random.random()
                elif mode == 1: th = 1e-9 if m > nb//2 else 1-1e-9      # pile up towards the centre box
                elif mode == 2: th = random.choice([1e-9, 1-1e-9])
                else: th = random.choice([1e-9, 0.5, 1-1e-9])
                gam.append((m-1+th)*h)
            r = nb//2
            worst = max(worst, per_r_sum(gam, r, delta))
        print(f"delta={delta} lam={lam}: worst sampled={worst:.3f}  our bound={our_bound(lam,delta):.3f}"
              + (f"  Bellotti claim={bellotti_bound(delta):.3f}" if lam == 1.0 else ""))
# explicit counterexample to 'unique representative with |gr-gs|<delta'
d = 0.01; g1, g2 = 0.99*d, 1.01*d
print("counterexample: boxes (0,d],(d,2d], reps", g1, g2, "|diff| =", g2-g1, "< delta =", d)
