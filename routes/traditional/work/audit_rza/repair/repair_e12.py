"""
repair_e12.py -- removes the last (indirect) use of Helfgott's book: the constant
E_1^{(2)} = 0.232 of Zuniga-Alterman, Colloq. Math. 168 (2022) (ZA), Lemma `sum2:critic:1`/Remark.

ZA defines E_1^{(2)} = Upper((1-1/sqrt2) * max(4 b2/pi^2, 3*c_H, 0.40672)), where
  c_H  = sup_{X>=1573} |Q_odd(X) - 4X/pi^2|/sqrt X  <= 9/70   (Helfgott's book, Lemma 5.2: the ONLY book input),
  0.40672 = sup_{1<=X<=1573} sqrt X |S_odd(X) - (4/pi^2)(log X + b2)|   (ZA's own interval computation),
  4 b2/pi^2 = 0.78966...  (the X in (0,1) part; b2 = gamma + sum_p 2 log p/(p^2-1) + log 2/3),
with Q_odd(X) = #{n <= X odd squarefree}, S_odd(X) = sum_{n<=X odd} mu^2(n)/n.
The max is attained by 4 b2/pi^2, so E_1^{(2)} stays 0.232 as soon as 3*c <= 4 b2/pi^2 for SOME
proved bound c >= c_H.  We prove c := max(c_own, 0.02767/(1-2^{-1/2}) + 2^{-1/2} c_tail) with
  c_own  = sup over 1573 <= X <= N of |Q_odd(X) - 4X/pi^2|/sqrt X      (own count, N = 10^8),
  c_tail = sup over N/2 <= y < N of the same,
using Q_odd(t) = sum_{k>=0} (-1)^k Q(t/2^k) and Cohen-Dress-El Marraki (Funct. Approx. 37 (2007),
Thm 3 bis; quoted as FA-II Lemma `sqf`): |Q(X) - 6X/pi^2| <= 0.02767 sqrt X for X >= 438653.
Also re-checks ZA's 0.40672 on [1, 1573] in Arb.
Run: python -I repair_e12.py
"""
import os, sys, json, math, time
import numpy as np
from flint import arb, ctx
ctx.prec = 128
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))


def b2_arb():
    """b1 = gamma + sum_p 2 log p/(p^2-1) (p <= 1e7, tail <= 2.0001 C_2), b2 = b1 + log 2/3"""
    from rza_euler import primes_upto
    import rza_common as rc
    ps = primes_upto(10 ** 7)
    s = math.fsum(2 * math.log(p) / (p * p - 1.0) for p in ps.tolist())
    # float sum of 664579 positive terms: relative error <= 1e-12 (generous); tail p > 1e7
    tail = 2 * rc.C_kappa(2, 10 ** 7, 0) * arb("1.0000001")      # C_2 with theta(M) dropped (upper bound)
    S = arb(s) + arb(0, s * 1e-12)
    return arb.const_euler() + S + arb(0).union(tail) + arb(2).log() / 3


def main():
    t0 = time.time()
    b2 = b2_arb()
    PI2 = arb.pi() ** 2
    four = 4 * b2 / PI2
    print("b2 in %s;  4 b2/pi^2 = %s  (ZA: 0.7896...)" % (b2.str(10), four.str(10)))
    # (1) ZA's interval computation on [1, 1573]: sup sqrt X |S_odd(X) - (4/pi^2)(log X + b2)|
    N0 = 1573
    mu2 = [1] * (N0 + 2)
    for p in range(2, 40):
        for k in range(p * p, N0 + 2, p * p):
            mu2[k] = 0
    S = arb(0); sup0 = arb(0)
    for n in range(1, N0 + 1):
        if n % 2 and mu2[n]:
            S += arb(1) / n
        # X in [n, n+1): g(X) = sqrt X (A - c log X), A = S - c b2, c = 4/pi^2; |g| is maximal at an
        # endpoint or at the critical point log X* = A/c - 2 (if inside)
        c = 4 / PI2
        A = S - c * b2
        pts = [arb(n), arb(min(n + 1, N0))]
        Xs = (A / c - 2).exp()
        if bool(Xs > n) and bool(Xs < n + 1):
            pts.append(Xs)
        elif not (bool(Xs <= n) or bool(Xs >= n + 1)):
            pts.append(arb(n).union(arb(n + 1)))       # undecided: enclose the whole cell
        for X in pts:
            v = X.sqrt() * abs(A - c * X.log())
            sup0 = sup0.max(v)
    print("ZA (intt:v=2): sup_{1<=X<=1573} = %s   (ZA: <= 0.40672)  %s" % (
        sup0.upper().str(8, radius=False), "OK" if bool(sup0 <= arb("0.40672")) else "CHECK"))
    # (2) own count of odd squarefree numbers up to N (chunked)
    N = 10 ** 8
    sq = np.ones(N + 2, dtype=bool); sq[0] = False
    for p in range(3, int(math.isqrt(N + 1)) + 1, 2):
        if all(p % d for d in range(3, int(p ** 0.5) + 1, 2)):
            sq[p * p::p * p] = False
    sq[0::2] = False                       # even numbers excluded
    Qo = np.cumsum(sq, dtype=np.int64)     # Q_odd(n) exact
    del sq
    c4 = 4 / math.pi ** 2
    lo, hi = 1573, N
    c_own, at, c_tail = 0.0, 0, 0.0
    tl = N // 2
    CH = 10 ** 7
    for s0 in range(lo, hi, CH):
        s1 = min(s0 + CH, hi)
        nn = np.arange(s0, s1, dtype=np.float64)
        q = Qo[s0:s1].astype(np.float64)
        # sup over X in [n, n+1) of |q - c4 X|/sqrt X: endpoints (|.|/sqrt X is monotone or has an
        # interior min only, since q - c4 X is linear and 1/sqrt X convex decreasing -> max at endpoints)
        r = np.maximum(np.abs(q - c4 * nn) / np.sqrt(nn), np.abs(q - c4 * (nn + 1)) / np.sqrt(nn + 1))
        i = int(np.argmax(r))
        if r[i] > c_own:
            c_own, at = float(r[i]), s0 + i
        if s1 > tl:
            c_tail = max(c_tail, float(r[max(0, tl - s0):].max()))
    TOL = 1e-9                              # float error of c4*n and sqrt: relative <= 1e-15; generous
    c_own_u = arb(c_own) * (1 + arb(TOL)); c_tail_u = arb(c_tail) * (1 + arb(TOL))
    c_cde = arb("0.02767")
    c_large = c_cde / (1 - 1 / arb(2).sqrt()) + c_tail_u / arb(2).sqrt()
    c = c_own_u.max(c_large)
    print("own: sup_{1573<=X<=1e8} |Q_odd-4X/pi^2|/sqrt X = %.6f (at X=%d);  tail [5e7,1e8): %.6f" % (c_own, at, c_tail))
    print("X > 1e8 via CDE 0.02767: <= %s" % c_large.upper().str(8, radius=False))
    print("=> c_H <= c = %s ; 3c = %s  vs  4 b2/pi^2 = %s  => %s" % (
        c.upper().str(8, radius=False), (3 * c).upper().str(8, radius=False), four.lower().str(8, radius=False),
        "E_1^(2) = 0.232 HOLDS WITHOUT HELFGOTT'S BOOK" if bool(3 * c < four) else "NOT ENOUGH"))
    E2 = (1 - 1 / arb(2).sqrt()) * four.max(3 * c).max(arb("0.40672").max(sup0))
    print("E_1^(2) = (1-1/sqrt2) max(...) = %s <= 0.232: %s" % (E2.upper().str(8, radius=False), bool(E2 <= arb("0.232"))))
    json.dump(dict(c_own=c_own, at=at, c_tail=c_tail, c=c.upper().str(12, radius=False), four_b2_pi2=four.str(12),
                   za_sup_1573=sup0.upper().str(10, radius=False), E2=E2.upper().str(10, radius=False),
                   ok=bool(3 * c < four) and bool(E2 <= arb("0.232"))),
              open(os.path.join(HERE, "out", "e12.json"), "w"), indent=1)
    print("time %.1f s" % (time.time() - t0))


if __name__ == "__main__":
    main()
