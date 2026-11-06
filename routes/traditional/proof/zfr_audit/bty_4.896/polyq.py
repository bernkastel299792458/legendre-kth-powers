"""Exact polynomial arithmetic over Q and Sturm root counting (no external deps).
Polynomials are lists of Fractions, lowest degree first."""
from fractions import Fraction as Q


def trim(p):
    p = list(p)
    while p and p[-1] == 0:
        p.pop()
    return p


def add(p, q):
    n = max(len(p), len(q))
    return trim([(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)])


def scale(p, c):
    return trim([c * a for a in p])


def mul(p, q):
    if not p or not q:
        return []
    r = [Q(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            r[i + j] += a * b
    return trim(r)


def deriv(p):
    return trim([i * p[i] for i in range(1, len(p))])


def ev(p, x):
    r = Q(0)
    for a in reversed(p):
        r = r * x + a
    return r


def divmod_(p, q):
    p, q = trim(p), trim(q)
    out = [Q(0)] * max(len(p) - len(q) + 1, 1)
    r = list(p)
    while len(r) >= len(q) and r:
        c = r[-1] / q[-1]
        k = len(r) - len(q)
        out[k] = c
        for i, b in enumerate(q):
            r[i + k] -= c * b
        r = trim(r)
    return trim(out), r


def sturm_chain(p):
    ch = [trim(p), deriv(p)]
    while ch[-1]:
        _, r = divmod_(ch[-2], ch[-1])
        if not r:
            break
        ch.append(scale(r, Q(-1)))
    return ch


def _sign_changes(vals):
    s = [v for v in vals if v != 0]
    return sum(1 for a, b in zip(s, s[1:]) if (a > 0) != (b > 0))


def sign_at(p, x):
    if x == "+inf":
        return Q(1) if p[-1] > 0 else Q(-1)
    if x == "-inf":
        return Q(1) if (p[-1] > 0) == (len(p) % 2 == 1) else Q(-1)
    return ev(p, x)


def count_roots(p, a, b):
    """Number of distinct real roots of p in (a, b]; a, b may be '-inf'/'+inf'."""
    ch = sturm_chain(p)
    return _sign_changes([sign_at(q, a) for q in ch]) - _sign_changes([sign_at(q, b) for q in ch])
