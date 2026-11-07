"""
rza_counterexample.py -- RIGOROUS (Arb) counterexample to inequality (6.6) [label exxp] of
RZA v3, the starting inequality of the proof of Theorem 1.2:

  (6.6)  S_eps(X) <= S_0(X)/X^{2eps} + 2 eps A(X) + eps^2 B(X) + 2/zeta(1+eps) - G(X;1+eps)/zeta(1+eps)^2,
  A(X) = X^{-2eps} sum_{l<=X} mu^2(l)phi(l)/l^2 m_l(X/l) Delta_l(X/l,eps),
  B(X) = X^{-2eps} sum_{l<=X} mu^2(l)phi(l)/l^2 Delta_l(X/l,eps)^2,
  Delta_q(Y,eps) defined by Lemma 3.1:  m_q(Y;1+eps) = m_q(Y)/Y^eps + q^{1+eps}/(phi_{1+eps}(q)zeta(1+eps)) + eps Delta_q(Y,eps)/Y^eps.

We compute S_eps(X) twice (directly from the double sum over d,e <= X, and from the classical
identity sum_l mu^2 phi_{1+eps}(l)/l^{2+2eps} m_l(X/l;1+eps)^2), and the right side of (6.6).
We also check the CORRECTED identity
  S_eps(X) = X^{-2eps} sum_l mu^2(l) phi_{1+eps}(l)/l^2 (m_l(X/l)+eps Delta_l(X/l,eps))^2 + 2/zeta - G/zeta^2
(the paper's (6.6) drops the factor l^{2eps}*phi_{1+eps}(l)/phi(l) >= 1 ... see REPORT).
Run: python -I rza_counterexample.py
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from flint import arb, ctx, fmpq
ctx.prec = 128


def factor_sqfree(n):
    ps, x, p = [], n, 2
    while p * p <= x:
        if x % p == 0:
            x //= p
            if x % p == 0:
                return None
            ps.append(p)
        p += 1
    if x > 1:
        ps.append(x)
    return ps


def run(X, eps, direct=True):
    eps = arb(eps)
    s = 1 + eps
    z = s.zeta()
    sq = {}
    for n in range(1, X + 1):
        f = factor_sqfree(n)
        if f is not None:
            sq[n] = f
    mu = {n: (-1) ** len(f) for n, f in sq.items()}
    pw = {n: arb(n) ** (-s) for n in sq}
    # direct double sum
    Sdir = None
    if direct:
        from math import gcd
        Sdir = arb(0)
        keys = list(sq)
        for d in keys:
            for e in keys:
                L = d * e // gcd(d, e)
                Sdir += mu[d] * mu[e] * arb(L) ** (-s)
    Sclass = arb(0); S0 = arb(0); G = arb(0); A = arb(0); B = arb(0); Scorr = arb(0)
    for l, ps in sq.items():
        phi = arb(l); phie = arb(l) ** s
        for p in ps:
            phi *= (1 - arb(1) / p)
            phie *= (1 - arb(p) ** (-s))
        Y = X // l
        m1 = arb(0); me = arb(0)
        for k in range(1, Y + 1):
            if k in sq and all(k % p for p in ps):
                m1 += arb(mu[k]) / k
                me += mu[k] * pw[k]
        Yr = arb(X) / l
        main = arb(l) ** s / phie / z
        Delta = Yr ** eps * (me - m1 * Yr ** (-eps) - main) / eps
        Sclass += phie / arb(l) ** (2 + 2 * eps) * me ** 2
        S0 += phi / arb(l) ** 2 * m1 ** 2
        G += 1 / phie
        A += phi / arb(l) ** 2 * m1 * Delta
        B += phi / arb(l) ** 2 * Delta ** 2
        Scorr += phie / arb(l) ** 2 * (m1 + eps * Delta) ** 2
    Xe = arb(X) ** (-2 * eps)
    A *= Xe; B *= Xe
    rhs = S0 * Xe + 2 * eps * A + eps ** 2 * B + 2 / z - G / z ** 2
    corr = Xe * Scorr + 2 / z - G / z ** 2
    return Sdir, Sclass, corr, rhs, S0


if __name__ == "__main__":
    print("RZA v3 inequality (6.6) [exxp], rigorous Arb evaluation")
    for X, eps, direct in [(1000, "0.04", True), (1000, "0.01", True), (3000, "0.04", False), (3000, "0.02", False)]:
        Sdir, Scl, corr, rhs, S0 = run(X, eps, direct)
        fails = bool(Scl > rhs)
        print("X=%d eps=%s: S_eps direct=%s classic=%s corrected-identity=%s | RHS(6.6)=%s | S_0(X)=%s  => (6.6) %s" % (
            X, eps, Sdir.str(10) if Sdir is not None else "-", Scl.str(10), corr.str(10), rhs.str(10), S0.str(8),
            "FALSE (certified: S_eps > RHS)" if fails else "not violated"))
