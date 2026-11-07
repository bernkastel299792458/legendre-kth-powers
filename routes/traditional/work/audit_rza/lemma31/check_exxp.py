# OUT-OF-SCOPE side check (RZA Section 6, display (exxp), lines ~1466-1489 of the v3 .tex):
# RZA writes  S_e(X) <= X^{-2e} sum_l mu^2(l) phi(l)/l^2 (m_l(X/l) + e Delta_l(X/l,e))^2 + 2/zeta - G/zeta^2,
# after bounding the weight mu^2 phi_{1+e}(l)/l^{2+2e} <= phi(l)/l^2 and inserting
# n_l(X/l;1+e) = (X/l)^{-e} (m_l(X/l) + e Delta_l(X/l,e)).   The factor (X/l)^{-2e} = X^{-2e} l^{2e}
# seems to have lost l^{2e}.  Exact identity:  S_e = X^{-2e} sum_l mu^2 phi_{1+e}(l)/l^2 (...)^2 + 2/zeta - G/zeta^2.
# We compute (Arb) S_e(X) directly as a double sum and compare with the RHS of (exxp).
import sys, math
from math import gcd
from flint import arb, fmpq, ctx
ctx.prec = 128

def mobius_list(n):
    mu = [1] * (n + 1); mu[0] = 0
    isp = [True] * (n + 1)
    for p in range(2, n + 1):
        if isp[p]:
            for k in range(2 * p, n + 1, p): isp[k] = False
            for k in range(p, n + 1, p): mu[k] = -mu[k]
            for k in range(p * p, n + 1, p * p): mu[k] = 0
    return mu
def primes_of(n):
    ps = []; d = 2
    while d * d <= n:
        if n % d == 0:
            ps.append(d)
            while n % d == 0: n //= d
        d += 1
    if n > 1: ps.append(n)
    return ps

def run(X, e):
    mu = mobius_list(X)
    sq = [n for n in range(1, X + 1) if mu[n]]
    ea = arb(fmpq(*e)) if isinstance(e, tuple) else arb(e)
    s1 = 1 + ea
    zeta = s1.zeta()
    pw = {}
    def ipow(L):
        if L not in pw: pw[L] = arb(L) ** (-s1)
        return pw[L]
    # direct double sum
    S = arb(0)
    for d in sq:
        for f in sq:
            S += mu[d] * mu[f] * ipow(d * f // gcd(d, f))
    # pieces
    G = arb(0); main_true = arb(0); main_claim = arb(0)
    Xa = arb(X)
    for l in sq:
        ps = primes_of(l)
        t = X // l   # m_l(X/l;.) depends on [X/l]
        m1e = arb(0)
        for k in range(1, t + 1):
            if mu[k] and all(k % p for p in ps): m1e += mu[k] * ipow(k)
        P = arb(1); phi1e = arb(l) ** s1; phi = l
        for p in ps:
            P *= 1 / (1 - arb(p) ** (-s1)); phi1e *= (1 - arb(p) ** (-s1)); phi = phi // p * (p - 1)
        n = m1e - P / zeta                     # n_l(X/l;1+e)
        inner = (Xa / l) ** ea * n             # = m_l(X/l) + e Delta_l(X/l,e)
        G += 1 / phi1e
        main_true += phi1e / arb(l) ** 2 * inner ** 2
        main_claim += arb(phi) / arb(l) ** 2 * inner ** 2
    rest = 2 / zeta - G / zeta ** 2
    true_rhs = Xa ** (-2 * ea) * main_true + rest
    claim_rhs = Xa ** (-2 * ea) * main_claim + rest
    return S, true_rhs, claim_rhs

for X in [30, 100, 300, 1000]:
    for e in [(1, 100), (1, 10)]:
        S, tr, cl = run(X, e)
        print('X=%5d e=%s/%s  S_e(X)=%s  identity RHS=%s  (exxp) RHS=%s  S_e - (exxp)RHS = %s  -> (exxp) %s' % (
            X, e[0], e[1], S.str(10), tr.str(10), cl.str(10), (S - cl).str(6),
            'VIOLATED' if S > cl else ('holds' if S <= cl else 'undecided')), flush=True)
