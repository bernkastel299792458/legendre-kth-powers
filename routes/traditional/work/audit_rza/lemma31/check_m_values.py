# Exact (Fraction) checks of the m_l(t) claims used in RZA Lemma 6.2 (A_est), and an Arb check
# of the positivity F_1(x) = sum_{n<=x,(n,q)=1} mu(n)/n log(x/n) >= 0 for x <= 47 and all q.
# m_q(t) depends only on N=[t] and on the primes of q that are <= N.
import sys, os, itertools
from fractions import Fraction as Fr
from flint import arb, ctx
ctx.prec = 100

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
SQF = {n: mobius(n) for n in range(1, 60)}

def subsets(ps):
    for k in range(len(ps) + 1):
        for s in itertools.combinations(ps, k):
            yield s
def prod(s):
    r = 1
    for p in s: r *= p
    return r
def m_exact(N, sub):
    return sum((Fr(SQF[l], l) for l in range(1, N + 1) if SQF[l] and all(l % p for p in sub)), Fr(0))

EXC = {1, 11, 13, 17}
ok = True
# (1) m_l(t) >= 0 for 1 <= t < 5
mn = min((m_exact(N, s), N, prod(s)) for N in range(1, 5) for s in subsets([p for p in PR if p <= N]))
print('(1) min m_q(t), 1<=t<5, all q:', mn[0], '=', float(mn[0]), 'at N=%d q=%d' % (mn[1], mn[2]))
ok &= mn[0] >= 0
# (2) m_l(t) >= -1/30 for t in [5,10.9)
mn = min((m_exact(N, s), N, prod(s)) for N in range(5, 11) for s in subsets([p for p in PR if p <= N]))
print('(2) min m_q(t), 5<=t<10.9, all q:', mn[0], '=', float(mn[0]), 'at N=%d q=%d' % (mn[1], mn[2]), ' claim >= -1/30:', mn[0] >= Fr(-1, 30))
ok &= mn[0] >= Fr(-1, 30)
# (3) min over 10.9<=t<47 of m_l(t), (l, prod_{p<47} p) not in EXC.
#     For N<=42 every r | prod_{p<=N} p occurs (r*43 is non-exceptional); for 43<=N<=46 need r not in EXC.
best = None; cnt = 0
for N in range(10, 47):
    ps = [p for p in PR if p <= N]
    for s in subsets(ps):
        r = prod(s)
        if N >= 43 and r in EXC: continue
        v = m_exact(N, s); cnt += 1
        if best is None or v < best[0]: best = (v, N, r)
print('(3) min m_q(t), 10.9<=t<47, non-exceptional classes (%d cases):' % cnt, best[0], '=', float(best[0]), 'at N=%d r=%d' % best[1:],
      ' claim >= -2323/30030 (=%.6f):' % float(Fr(-2323, 30030)), best[0] >= Fr(-2323, 30030))
ok &= best[0] >= Fr(-2323, 30030)
# (4) max (and min) of m_Q(t) over 10.9<=t<47 for Q in EXC
mx = None; mi = None
for Q in sorted(EXC):
    for N in range(10, 47):
        s = [p for p in PR if p <= N and Q % p == 0]
        v = m_exact(N, s)
        if mx is None or v > mx[0]: mx = (v, N, Q)
        if mi is None or v < mi[0]: mi = (v, N, Q)
print('(4) max m_Q(t), 10.9<=t<47, Q in {1,11,13,17}:', mx[0], '=', float(mx[0]), 'at N=%d Q=%d' % mx[1:],
      ' claim <= 57731/570570 (=%.6f):' % float(Fr(57731, 570570)), mx[0] <= Fr(57731, 570570))
print('    min m_Q(t) over the same set:', mi[0], '=', float(mi[0]), 'at N=%d Q=%d' % mi[1:],
      ' |min| <= 57731/570570:', -mi[0] <= Fr(57731, 570570), ' |min| <= 2323/30030:', -mi[0] <= Fr(2323, 30030))
ok &= mx[0] <= Fr(57731, 570570) and -mi[0] <= Fr(57731, 570570)
print('    2323/30030 == -m_1(13):', Fr(2323, 30030) == -m_exact(13, []))
print('    57731/570570 == m_17(22):', Fr(57731, 570570) == m_exact(22, [17]))
for Q in sorted(EXC):
    vals = [(m_exact(N, [p for p in PR if p <= N and Q % p == 0]), N) for N in range(10, 47)]
    mxQ = max(vals); mnQ = min(vals)
    print('    Q=%2d: max m_Q = %s (%.6f) at N=%d ; min m_Q = %s (%.6f) at N=%d' % (Q, mxQ[0], float(mxQ[0]), mxQ[1], mnQ[0], float(mnQ[0]), mnQ[1]))
# (6) what the A_est third reduction really needs, given Delta_Q <= 0 for Q in {11,13,17} (sign_table_arb d0):
#     C >= max( 2323/30030 [non-exc, -m], max_{Q in 11,13,17} (-min m_Q)_+, max |m_1| )
need = [Fr(2323, 30030)]
for Q in (11, 13, 17):
    need.append(max(Fr(0), -min(m_exact(N, [p for p in PR if p <= N and Q % p == 0]) for N in range(10, 47))))
m1abs = max(abs(m_exact(N, [])) for N in range(10, 47))
need.append(m1abs)
print('(6) needed constant in A_est (using Delta_Q<=0 for Q=11,13,17):', max(need), '=', float(max(need)),
      '; max|m_1| on [10.9,47) =', m1abs, '<= 57731/570570:', max(need) <= Fr(57731, 570570))
# (5) F_1(N) >= 0 (rigorous, Arb) for N <= 47 and all q (only primes <= N matter; F_1 is continuous and
#     linear in log x on [N,N+1], so integer points suffice).
minF = None
for N in range(1, 48):
    ps = [p for p in PR if p <= N]
    ls = [l for l in range(1, N + 1) if SQF[l]]
    logs = {l: (arb(N) / l).log() for l in ls}
    for s in subsets(ps):
        F = arb(0)
        for l in ls:
            if all(l % p for p in s): F += arb(SQF[l]) / l * logs[l]
        if minF is None or F.lower() < minF[0].lower(): minF = (F, N, prod(s))
        if not (F >= 0): print('   F_1 NOT >= 0 at N=%d q=%d: %s' % (N, prod(s), F)); ok = False
print('(5) min F_1(N) over N<=47, all q:', minF[0], 'at N=%d q=%d' % minF[1:])
print('ALL OK' if ok else 'SOME CLAIM FAILS')
