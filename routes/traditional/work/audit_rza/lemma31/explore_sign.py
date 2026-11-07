# Float exploration (NOT a proof) of the sign table of RZA Lemma 3.1.
# D_q(X,eps) := Delta_q(X,eps)/X^eps
#   = (1/eps)[ m_q(X;1+eps) - m_q(X) X^-eps - P_q(eps)/zeta(1+eps) ],
#   P_q(eps) = prod_{p|q} (1-p^{-1-eps})^{-1}.
# Written as  sum_{l<=N,(l,q)=1} mu(l)/l * G(eps; log l, log X) - P_q(eps) Z(eps),
#   G(eps;a,b) = int_a^b e^{-eps u} du,  Z(eps) = 1/(eps zeta(1+eps)), Z(0)=1.
# For X in [N,N+1) D is monotone in X, so sup = max(D(N), D(N+1^-)).
import numpy as np
from scipy.special import zeta
import itertools, sys

PR = [p for p in range(2, 60) if all(p % d for d in range(2, int(p**.5) + 1))]

def mobius(n):
    r, m = 1, n
    for p in PR:
        if p * p > m: break
        if m % p == 0:
            m //= p
            if m % p == 0: return 0
            r = -r
    if m > 1: r = -r
    return r

E = np.concatenate([np.linspace(0, 0.1, 4001), np.linspace(0.1, 1, 3601)[1:]])
with np.errstate(divide='ignore', invalid='ignore'):
    Z = np.where(E == 0, 1.0, 1.0 / (E * zeta(1 + E)))

def Pfac(p):
    return 1.0 / (1.0 - p ** (-1.0 - E))

def G(a, b):
    with np.errstate(divide='ignore', invalid='ignore'):
        g = np.exp(-E * a) * (-np.expm1(-E * (b - a))) / E
    g[E == 0] = b - a
    return g

def Dmat(N, Xs, extra=()):
    """returns dict r -> array over E of sup_{X in Xs} D_{r*extra}(X,eps), r | prod_{p<=N} p"""
    ps = [p for p in PR if p <= N]
    ls = [l for l in range(1, N + 1) if mobius(l) != 0]
    Gs = {X: np.array([G(np.log(l), np.log(X)) for l in ls]) for X in Xs}
    Pext = np.ones_like(E)
    for p in extra: Pext = Pext * Pfac(p)
    out = {}
    for k in range(len(ps) + 1):
        for sub in itertools.combinations(ps, k):
            r = int(np.prod(sub)) if sub else 1
            coef = np.array([mobius(l) / l if all(l % p for p in sub) else 0.0 for l in ls])
            P = Pext.copy()
            for p in sub: P = P * Pfac(p)
            best = None
            for X in Xs:
                d = coef @ Gs[X] - P * Z
                best = d if best is None else np.maximum(best, d)
            out[r] = best
    return out

def report(name, vals):
    print(name, flush=True)
    for v in vals: print('   ', v, flush=True)

if __name__ == '__main__':
    EXC = {1, 11, 13, 17}
    # (a) X < 10.9, eps <= 4/25 (and also look at eps<=1), all q
    resa = []
    for N in range(1, 11):
        Xs = [N, N + 1] if N < 10 else [10, 10.9]
        d = Dmat(N, Xs)
        for r, arr in d.items():
            m1 = arr[E <= 4 / 25 + 1e-15].max(); m2 = arr.max()
            resa.append((m1, m2, N, r, E[np.argmax(arr)]))
    resa.sort(reverse=True)
    report('(a) top: (max eps<=4/25, max eps<=1, N, q, argmax eps)', resa[:8])
    # (b),(c),(d)
    resb, resc, resd = [], [], []
    for N in range(1, 48):
        Xs = [N, N + 1] if N < 47 else [47]
        d = Dmat(N, Xs)
        d43 = Dmat(N, Xs, extra=(43,)) if N < 43 else None
        for r, arr in d.items():
            if N <= 46:
                if r not in EXC:
                    resb.append((arr.max(), arr[E <= 0.1 + 1e-15].max(), N, r, '', E[np.argmax(arr)]))
                elif N < 43:
                    a2 = d43[r]
                    resb.append((a2.max(), a2[E <= 0.1 + 1e-15].max(), N, r, '*43', E[np.argmax(a2)]))
            if r == 1:
                resc.append((arr.max(), arr[E <= 0.1 + 1e-15].max(), N, E[np.argmax(arr)]))
        if N <= 46:
            for Q in (11, 13, 17):
                if Q <= N: arr = d[Q]
                else:
                    arr = Dmat(N, Xs, extra=(Q,))[1]
                resd.append((arr.max(), arr[E <= 0.1 + 1e-15].max(), N, Q, E[np.argmax(arr)]))
        print('done N', N, flush=True)
    resb.sort(reverse=True); resc.sort(reverse=True); resd.sort(reverse=True)
    report('(b) top: (max eps<=1, max eps<=0.1, N, r, extra, argmax)', resb[:10])
    report('(c) top: (max eps<=1, max eps<=0.1, N, argmax)', resc[:10])
    report('(d) top: (max eps<=1, max eps<=0.1, N, Q, argmax)', resd[:10])
