"""
rza_mpatterns.py -- exact (fractions) check of the m_l(t) pattern constants used in the proof of
RZA v3 Lemma 6.2:  m_l(t) = sum_{k<=t,(k,l)=1} mu(k)/k depends on l only through (l, prod_{p<47} p).
  (a) m_l(t) >= 0 for t < 5 (all l);  (b) m_l(t) >= -1/30 for 5 <= t < 10.9;
  (c) min over 10.9 < t < 47, classes not in {1,11,13,17}:  >= -2323/30030 ?
  (d) max over 10.9 < t < 47 for classes {1,11,13,17}:     <= 57731/570570 ?  and |m| (min) for them.
Run: python -I rza_mpatterns.py
"""
from fractions import Fraction as Fr
from itertools import combinations
P = [2,3,5,7,11,13,17,19,23,29,31,37,41,43]
def mu(k):
    r, x = 1, k
    for p in P + [47]:
        if x % p == 0:
            x //= p
            if x % p == 0: return 0
            r = -r
    return r
def mvals(S, lo, hi):
    """values of m(t) for t in [lo,hi) with coprimality to the set S of primes; returns list of (t_int, value)"""
    out, acc = [], Fr(0)
    for k in range(1, int(hi) + 1):
        if all(k % p for p in S):
            acc += Fr(mu(k), k)
        # m(t) for t in [k, k+1)
        if k + 1 > lo and k < hi:
            out.append((k, acc))
    return out
res = {}
minA, minB, minC = Fr(10), Fr(10), Fr(10)
maxD = {}
minD = {}
for r in range(len(P) + 1):
    for S in combinations(P, r):
        S = set(S)
        for k, v in mvals(S, 1, 5):
            minA = min(minA, v)
        for k, v in mvals(S, 5, 10.9):
            minB = min(minB, v)
        cls = 1
        for p in S: cls *= p
        vals = [v for k, v in mvals(S, 10.9, 47)]
        if cls in (1, 11, 13, 17):
            maxD[cls] = max(vals); minD[cls] = min(vals)
        else:
            minC = min(minC, min(vals))
print("(a) min m_l(t), t<5: %s  (claim >= 0) %s" % (minA, "OK" if minA >= 0 else "FAILS"))
print("(b) min m_l(t), 5<=t<10.9: %s  (claim >= -1/30) %s" % (minB, "OK" if minB >= Fr(-1,30) else "FAILS"))
print("(c) min over other classes, 10.9<t<47: %s = %.6f (claim >= -2323/30030 = %.6f) %s" % (minC, float(minC), -2323/30030, "OK" if minC >= Fr(-2323,30030) else "FAILS"))
for c in (1, 11, 13, 17):
    print("(d) class %2d: max %s = %.6f, min %s = %.6f   (claim max <= 57731/570570 = %.6f) %s" % (
        c, maxD[c], float(maxD[c]), minD[c], float(minD[c]), 57731/570570, "OK" if maxD[c] <= Fr(57731,570570) else "FAILS"))
