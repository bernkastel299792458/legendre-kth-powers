"""Lever 2 quantified: if RH were verified up to height e^h (instead of e^28.73), does k=67 close
with existing zero-free regions / density estimates? Assumption (not from the papers): the
Cully-Hugill-Lee Delta scales proportionally with H_R. KLN constants kept as they are (conservative)."""
import bound
from bound import delta, terms, chl_ceiling
from math import inf, log, exp, pi
k = 67

def rh_regime(L, h):
    # all zeros with |gamma| <= 2T lie on the critical line when u = theta*L <= h
    best = inf
    for i in range(1, 600):
        c = 1 + i * 1e-3
        th = c / k
        if th * L > h:
            break
        t = terms(L, th, k, mode='KLN', Z=1e9)  # Z huge => no zero-free benefit; we replace density below
        if t is None:
            # below original H_R: KLN validity check fails; compute truncation part manually
            M, p = bound.truncation_constants(th)
            e = k * exp(-L / k)
            tr = 2 * M / k * ((1 + e) * (L + e) ** p + L ** p) * exp(-L * (th - 1 / k))
        else:
            tr = t['trunc']
        on_line = th * L * exp(L * (th - 0.5)) / pi
        best = min(best, tr + on_line)
    return best

def closes(h, Lmax=7000, step=10):
    low = chl_ceiling(k, 2.51949e11 * exp(h - log(bound.HR)))
    bound.LOG_HR = h
    L = int(low)
    worst = 0
    while L <= Lmax:
        d = rh_regime(L, h)
        if d >= 1:
            for mode in ('HYB', 'KLN'):
                for i in range(1, 600):
                    c = 1 + i * 1e-3
                    if c * L / k < h:
                        continue
                    d = min(d, delta(L, c / k, k, mode=mode))
        worst = max(worst, d)
        if d >= 1:
            bound.LOG_HR = log(bound.HR)
            return False, L, low
        L += step
    bound.LOG_HR = log(bound.HR)
    return True, None, low

for h in (28.73, 35, 45, 55, 65, 75, 85, 95, 100, 105, 110):
    ok, Lfail, low = closes(h)
    print(f"RH verified to e^{h:6.2f} (~10^{h/2.3026:5.1f}): lower ceiling L={low:7.1f}; closes={ok}; first failure L={Lfail}", flush=True)
