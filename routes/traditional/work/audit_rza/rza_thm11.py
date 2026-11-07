"""
rza_thm11.py -- the finite sums of the proof of Theorem 1.1 (Part 2) of RZA v3:

  S11(J) = sum_{1<j<=J} r_{Pi(j)} log((j+1)/j) sum_{n | Pi(j), n < N_j} mu^2(n)phi(n)/n^2   m_n(j)^2
  S12(J) = sum_{1<j<=J} t_{Pi(j)} (sqrt(j+1)+sqrt j) sum_{n | Pi(j), n < N_j} mu^2(n)phi(n)/n^{3/2} m_n(j)^2

with m_n(j) = sum_{l<=j,(l,n)=1} mu(l)/l, r_q = prod_{p|q} p^2/(p^2+p-1), t_q = prod p^{3/2}/(p^{3/2}-p+1).

(a) EXACT (Arb) full sums (no cutoff N_j, i.e. all n | Pi(j)) via the identity
      sum_{n|Pi(j)} w(n) m_n(j)^2 = prod_{p<=j}(1+w_p) * sum_{l,l'<=j} mu(l)mu(l')/(l l') prod_{p|[l,l']} (1+w_p)^{-1}.
    Dropping the cutoff can only increase S11, S12, so the full sums give upper bounds valid
    for every k (every sub-interval [eta^k 10^u, eta^{k+1} 10^u)).
(b) float enumeration WITH the cutoffs (exploration only), to reproduce the paper's
    hard-coded Bound1/Bound2/Bound3 and to see what W the paper used.

Run:  python -I rza_thm11.py
"""
import os, sys, json, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rza_common import *
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))


def primes_upto(n):
    return [p for p in range(2, n + 1) if all(p % d for d in range(2, int(p ** 0.5) + 1))]


def sqfree_upto(j):
    out = []
    for l in range(1, j + 1):
        ok, mu, ps, x = True, 1, [], l
        for p in primes_upto(j):
            if x % p == 0:
                x //= p
                if x % p == 0:
                    ok = False
                    break
                mu = -mu
                ps.append(p)
        if ok:
            out.append((l, mu, frozenset(ps)))
    return out


def inner_full(j, wfun):
    """sum_{n | Pi(j)} w(n) m_n(j)^2, exact in Arb"""
    P = primes_upto(j)
    one_w = {p: 1 + wfun(p) for p in P}
    tot_prod = arb(1)
    for p in P:
        tot_prod *= one_w[p]
    L = sqfree_upto(j)
    s = arb(0)
    for (l, mu, ps) in L:
        for (l2, mu2, ps2) in L:
            u = ps | ps2
            den = arb(1)
            for p in u:
                den *= one_w[p]
            s += arb(mu * mu2) / (l * l2) / den
    return tot_prod * s


def w11(p):
    return arb(p - 1) / arb(p) ** 2


def w12(p):
    return arb(p - 1) / arb(p) ** arb(1.5)


def r_q(j):
    v = arb(1)
    for p in primes_upto(j):
        v *= arb(p) ** 2 / (arb(p) ** 2 + p - 1)
    return v


def t_q(j):
    v = arb(1)
    for p in primes_upto(j):
        pp = arb(p) ** arb(1.5)
        v *= pp / (pp - p + 1)
    return v


def full_sums(Jmax=80):
    """cumulative exact S11(J), S12(J) for J = 2..Jmax (no cutoff)"""
    S11, S12 = {}, {}
    a11, a12 = arb(0), arb(0)
    for j in range(2, Jmax + 1):
        a11 += r_q(j) * (arb(j + 1) / j).log() * inner_full(j, w11)
        a12 += t_q(j) * (arb(j + 1).sqrt() + arb(j).sqrt()) * inner_full(j, w12)
        S11[j], S12[j] = a11, a12
    return S11, S12


# ---------------- float enumeration with cutoff (exploration) -----------------------------
def inner_cut_float(j, cutoff):
    P = primes_upto(j)
    k = len(P)
    # m_n(j) for every subset mask of P
    L = sqfree_upto(j)
    idx = {p: i for i, p in enumerate(P)}
    masks = np.arange(1 << k, dtype=np.int64)
    m = np.zeros(1 << k)
    for (l, mu, ps) in L:
        lm = 0
        for p in ps:
            lm |= 1 << idx[p]
        m += np.where((masks & lm) == 0, mu / l, 0.0)
    logn = np.zeros(1 << k)
    w11v = np.ones(1 << k)
    w12v = np.ones(1 << k)
    for p, i in idx.items():
        bit = (masks >> i) & 1
        logn += bit * math.log(p)
        w11v *= np.where(bit == 1, (p - 1) / p ** 2, 1.0)
        w12v *= np.where(bit == 1, (p - 1) / p ** 1.5, 1.0)
    keep = logn < math.log(cutoff)
    return float(np.sum((w11v * m * m)[keep])), float(np.sum((w12v * m * m)[keep]))


_cache = {}


def U_float(eta, u, v, k, J, W, consts):
    """paper's U(eta;u,v;k,J) in floats with cutoff n < eta^{k+1} 10^u / j"""
    TH1, H1, L1, L2, G1, G2 = consts
    Z = J + 0.9999
    base = 2 * TH1 / Z + 2 * math.sqrt(2) * H1 * L1 / math.sqrt(Z) + H1 ** 2 * L2 + W * math.log(2)
    Xlo = eta ** k * 10 ** u
    base += G1 * (1 + math.sqrt(2)) / math.sqrt(Xlo)
    key = (eta, u, k, J)
    if key not in _cache:
        s11 = s12 = 0.0
        for j in range(2, J + 1):
            a, b = inner_cut_float(j, eta ** (k + 1) * 10 ** u / j)
            s11 += float(r_q(j).mid()) * math.log((j + 1) / j) * a
            s12 += float(t_q(j).mid()) * (math.sqrt(j + 1) + math.sqrt(j)) * b
        _cache[key] = (s11, s12)
    s11, s12 = _cache[key]
    return base + W * s11 + G2 / math.sqrt(Xlo) * s12, s11, s12


if __name__ == "__main__":
    from rza_assembly import assemble, PAPER
    o = assemble(PAPER)
    S11, S12 = full_sums(80)
    print("(a) exact full sums (all n | Pi(j)); paper's S11_80, S12_80 are for J=80, X>=1e33 (all n):")
    print("    S11(80) = %s   paper 0.333415398793" % S11[80].str(15))
    print("    S12(80) = %s   paper 41346.25411" % S12[80].str(15))
    for J in (22, 61, 80):
        print("    J=%d: S11_full=%s  S12_full=%s" % (J, S11[J].str(12), S12[J].str(12)))
    out = {J: [S11[J].mid().str(25, radius=False), S11[J].rad().str(3, radius=False),
               S12[J].mid().str(25, radius=False), S12[J].rad().str(3, radius=False)] for J in S11}
    os.makedirs(os.path.join(HERE, "out"), exist_ok=True)
    json.dump(out, open(os.path.join(HERE, "out", "thm11_fullsums.json"), "w"), indent=0)

    consts = [float(o[k].mid()) for k in ("TH1",)] + [0.010032] + [float(o[k].mid()) for k in ("L1", "L2", "G1", "G2")]
    print("(b) float replay of the paper's U(eta;u,v;0,J) with its cutoff (exploration):")
    for (eta, u, v, J, pb, name) in [(1.2, 8, 12, 22, 0.65924939690269, "Bound1"),
                                     (2.2, 12, 16, 61, 0.4987002674334, "Bound2"),
                                     (5.2, 16, 33, 80, 0.4669804238966, "Bound3")]:
        for W, lab in ((0.40282372, "paper W=0.40282372"), (0.42824950612, "true  W=0.4282495")):
            val, s11, s12 = U_float(eta, u, v, 0, J, W, consts)
            print("    %s U(%.1f;%d,%d;0,%d) with %s = %.10f   (paper %.10f)  S11=%.8f S12=%.4f" % (
                name, eta, u, v, J, lab, val, pb, s11, s12))
