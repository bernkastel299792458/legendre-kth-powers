"""
explore_exxp.py -- EXPLORATION (floats): test RZA v3 inequality (6.6)/(exxp)
   S_eps(X) <= S_0(X)/X^{2eps} + 2 eps A(X) + eps^2 B(X) + 2/zeta(1+eps) - G(X;1+eps)/zeta(1+eps)^2
with A, B exactly as defined in (6.7),(6.8) (Delta from its defining identity), against the
exact S_eps(X); and the corrected identity
   S_eps(X) = X^{-2eps} sum_l mu^2(l) phi_{1+eps}(l)/l^2 (m_l(X/l)+eps Delta_l)^2 + 2/zeta - G/zeta^2.
Run: python -I explore_exxp.py
"""
import numpy as np, math, sys
from flint import arb
def zeta1p(e): return float(arb(1+e).zeta())
def run(X, eps):
    N = X
    s = np.ones(N+1, bool); s[:2] = False
    for i in range(2, int(N**0.5)+1):
        if s[i]: s[i*i::i] = False
    P = np.nonzero(s)[0]
    mu = np.ones(N+1, int); sq = np.ones(N+1, bool)
    pf = [[] for _ in range(N+1)]
    for p in P:
        mu[p::p] *= -1
        sq[p*p::p*p] = False
        for k in range(p, N+1, p): pf[k].append(p)
    mu[~sq] = 0
    z = zeta1p(eps)
    Se = S0 = Gx = 0.0
    A = B = 0.0
    Scorr = 0.0
    for l in range(1, X+1):
        if mu[l] == 0: continue
        ps = pf[l]
        phi = l*np.prod([1-1/p for p in ps]) if ps else 1.0
        phie = l**(1+eps)*np.prod([1-p**(-1-eps) for p in ps]) if ps else 1.0
        Y = X//l
        ks = np.arange(1, Y+1)
        cop = np.ones(Y, bool)
        for p in ps: cop &= (ks % p != 0)
        mk = mu[1:Y+1]*cop
        m1 = float(np.sum(mk/ks)); me = float(np.sum(mk/ks**(1+eps)))
        Yr = X/l
        main = l**(1+eps)/phie/z
        Delta = Yr**eps*(me - m1*Yr**(-eps) - main)/eps
        Se += phie/l**(2+2*eps)*me**2
        S0 += phi/l**2*m1**2
        Gx += 1/phie
        A += phi/l**2*m1*Delta
        B += phi/l**2*Delta**2
        Scorr += phie/l**2*(m1+eps*Delta)**2
    A *= X**(-2*eps); B *= X**(-2*eps)
    rhs_paper = S0/X**(2*eps) + 2*eps*A + eps**2*B + 2/z - Gx/z**2
    corr = X**(-2*eps)*Scorr + 2/z - Gx/z**2
    print("X=%7d eps=%.4f  S_eps=%.6f  identity(corrected)=%.6f  paper RHS (6.6)=%.6f  %s" % (
        X, eps, Se, corr, rhs_paper, "PAPER (6.6) FAILS" if Se > rhs_paper + 1e-9 else "ok"))
for X in (1000, 10000, 50000):
    for eps in (0.01, 0.02, 0.04, 0.1):
        run(X, eps)
