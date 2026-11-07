"""Rigorous upper bound for max_{0<=t<=3} |zeta(1/2+it)| (Arb, adaptive bisection).
Needed for a2 in KLN Lemma 3.2 (3.3): a2 >= max_{|t|<=3}|zeta(1/2+it)| + 6 a1/e.
(|zeta(1/2-it)| = |zeta(1/2+it)|, so t in [0,3] suffices.)"""
from flint import arb, acb, ctx
ctx.prec = 80

def ub(lo, hi):
    t = arb((lo + hi) / 2, (hi - lo) / 2)
    return acb(arb(1) / 2, t).zeta().abs_upper()

def max_bound(thresh, lo=0.0, hi=3.0, depth=0, stats=None):
    """returns True if |zeta(1/2+it)| <= thresh on [lo,hi] is certified."""
    stack = [(lo, hi)]
    n = 0
    while stack:
        a, b = stack.pop()
        n += 1
        if bool(ub(a, b) <= thresh):
            continue
        if b - a < 1e-12:
            return False, n
        m = (a + b) / 2
        stack += [(a, m), (m, b)]
    return True, n

if __name__ == "__main__":
    z0 = acb(arb(1) / 2).zeta()
    print("zeta(1/2) =", z0.real)
    for th in ("1.46036", "1.4604", "1.46042", "1.461"):
        ok, n = max_bound(arb(th))
        print("max_{0<=t<=3}|zeta(1/2+it)| <= %s : %s  (%d boxes)" % (th, ok, n))
    e = arb(1).exp()
    for a1 in ("0.63", "0.618"):
        print("a1=%s: a2 needed = 1.46036 + 6 a1/e = %s" % (a1, (arb("1.46036") + 6 * arb(a1) / e).str(10)))
