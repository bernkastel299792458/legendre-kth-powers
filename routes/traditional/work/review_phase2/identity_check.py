"""Referee: exhaustive check of mu(m) 1_{(m,delta)=1} = sum_{jk=m, k | delta^infty} mu(j)
for squarefree delta <= 300 and m <= 3000 (exact integers), and of the bijection (delta,k) -> delta*k."""
from math import gcd
N = 3000
mu = [0, 1] + [None] * (N - 1)
for n in range(2, N + 1):
    m, p, res = n, 2, 1
    while p * p <= m:
        if m % p == 0:
            m //= p
            if m % p == 0: res = 0; break
            res = -res
        p += 1
    else:
        if m > 1: res = -res
    mu[n] = res if res is not None else 0
def rad(n):
    r, p = 1, 2
    while p * p <= n:
        if n % p == 0:
            r *= p
            while n % p == 0: n //= p
        p += 1
    return r * (n if n > 1 else 1)
def divides_inf(k, d):   # k | d^infty  <=>  rad(k) | d
    return d % rad(k) == 0
bad = 0
for d in range(1, 301):
    if mu[d] == 0: continue
    for m in range(1, N + 1):
        lhs = mu[m] if gcd(m, d) == 1 else 0
        rhs = sum(mu[m // k] for k in range(1, m + 1) if m % k == 0 and divides_inf(k, d))
        bad += (lhs != rhs)
print("identity violations:", bad)
# bijection: n <-> (rad n, n/rad n); check uniqueness of decompositions n = delta*k, delta sqfree, k | delta^inf
viol = 0
for n in range(1, N + 1):
    reps = [d for d in range(1, n + 1) if n % d == 0 and mu[d] != 0 and divides_inf(n // d, d)]
    viol += (reps != [rad(n)])
print("bijection violations:", viol)
