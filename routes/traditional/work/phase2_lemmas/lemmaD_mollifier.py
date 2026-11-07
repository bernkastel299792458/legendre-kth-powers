"""
Lemma D (rigorous, Arb; NEW, own lemma): the mollifier M(s) = sum_{v<=V} sum_{w<=W} psi_v theta_w [v,w]^{-s}
of Bellotti's zero detector (Lemma 3.4, (3.11)) on the critical line.

Statement.  For real 1 <= U < V and W > 1, with psi, theta the Barban-Vehov weights of Bellotti (3.1),
and every real t,

    |M(1/2 + it)|  <=  S_abs := sum_{v,w} |psi_v| |theta_w| [v,w]^{-1/2}
                   <=  K_D * (VW)^{1/2},
    K_D := 4 c^2 P* (1 - (U/V)^{1/2}) (1 - W^{-1/2}) / (log(V/U) * log W),

where  c := sup_{y>=1} y^{-1/2} sum_{m<=y} mu(m)^2 m^{-1/2} = Q(7)/sqrt(7) = 1.32963...  (certified here)
and    P* := prod_p (1 + p^{-3/2} - p^{-2}) <= 1.4723  (certified here).

Bellotti (and Phase 0) use  |M(1/2+it)| <= sum_{n<=VW} d(n)^2 n^{-1/2} <= (VW)^{1/2} sum_{n<=VW} d(n)^2/n,
i.e. K = D2VW ~ log^4(VW)/(4 pi^2) ~ 1e7 at e^29, against K_D ~ 1e-2.

Proof: see REPORT addendum (Selberg-type diagonalisation (d,e)^{1/2} = sum_{delta|(d,e)} phi_{1/2}(delta),
integral representation of the weights, Q(y) <= c sqrt(y)).
"""
import math
from flint import arb, ctx
import numpy as np

ctx.prec = 100


def f_up(x):
    return math.nextafter(float(arb(x).upper()), math.inf)


def _mobius(N):
    mu = np.ones(N + 1, dtype=np.int8)
    isp = np.ones(N + 1, dtype=bool); isp[:2] = False
    for p in range(2, int(N ** 0.5) + 1):
        if isp[p]:
            isp[p * p::p] = False
    for p in np.nonzero(isp)[0]:
        mu[p::p] *= -1
        pp = int(p) * int(p)
        if pp <= N:
            mu[pp::pp] = 0
    mu[0] = 0
    return mu, isp


_CACHE = {}


def certify_c(Y1=10 ** 6):
    """Rigorous: c = sup_{y>=1} Q(y)/sqrt(y) equals Q(7)/sqrt(7).
    (i) On [m, m+1) Q is constant and sqrt(y) increasing, so the sup over [1, Y1] is a max over integers;
        all integers m <= Y1 are checked in Arb.
    (ii) For y >= Y1: Q(y) <= (12/pi^2) sqrt(y) + 1.5 log y + 2.4 (elementary, REPORT addendum D.2), and
        (1.5 log y + 2.4)/sqrt(y) is decreasing for y >= 2, so Q(y)/sqrt(y) <= 12/pi^2 + (1.5 log Y1 + 2.4)/sqrt(Y1)."""
    if 'c' in _CACHE:
        return _CACHE['c']
    mu, _ = _mobius(Y1)
    Q = arb(0)
    c7 = None
    worst_other = arb(0)
    for m in range(1, Y1 + 1):
        if mu[m] != 0:
            Q += 1 / arb(m).sqrt()
        r = Q / arb(m).sqrt()
        if m == 7:
            c7 = r
        else:
            if r.upper() > worst_other.upper():
                worst_other = arb(r.upper())
    assert bool(worst_other < c7), "sup not attained at y = 7"
    tail = 12 / arb.pi() ** 2 + (arb("1.5") * arb(Y1).log() + arb("2.4")) / arb(Y1).sqrt()
    assert bool(tail < c7)
    c = arb(c7.upper())          # exact value Q(7)/sqrt(7) enclosed; use its upper end
    _CACHE['c'] = c
    return c


def certify_Pstar(P=10 ** 6):
    """Rigorous upper bound of P* = prod_p (1 + p^{-3/2} - p^{-2}):
    exact product over p <= P in Arb, times prod_{p>P} <= exp(sum_{n>P} n^{-3/2}) <= exp(2/sqrt(P))."""
    if 'P' in _CACHE:
        return _CACHE['P']
    _, isp = _mobius(P)
    prod = arb(1)
    for p in np.nonzero(isp)[0]:
        ap = arb(int(p))
        prod *= 1 + 1 / (ap * ap.sqrt()) - 1 / (ap * ap)
    prod *= (2 / arb(P).sqrt()).exp()
    val = arb(prod.upper())
    _CACHE['P'] = val
    return val


def KD_upper(u, v, w, logT_lo, logT_hi=None):
    """RIGOROUS: upper bound of K_D (the factor multiplying (VW)^{1/2}) valid for all log T in [logT_lo, logT_hi].
    K_D is decreasing in log T (both 1/(log(V/U) log W) and the (1-...) factors are bounded by their values
    at the bottom end -- we simply drop the (1-...) factors <= 1).  u<v, w>0 decimal strings or numbers."""
    c = certify_c(); Ps = certify_Pstar()
    u = arb(str(u)); v = arb(str(v)); w = arb(str(w)); L = arb(str(logT_lo))
    return arb((4 * c * c * Ps / ((v - u) * L * w * L)).upper())


def S_abs_bound(U, V, W):
    """RIGOROUS (arb in): 4 c^2 P* (V^{1/2}-U^{1/2})(W^{1/2}-1)/(log(V/U) log W)."""
    c = certify_c(); Ps = certify_Pstar()
    U = arb(U); V = arb(V); W = arb(W)
    return 4 * c * c * Ps * (V.sqrt() - U.sqrt()) * (W.sqrt() - 1) / ((V / U).log() * W.log())


if __name__ == "__main__":
    import time
    t = time.time()
    c = certify_c(); Ps = certify_Pstar()
    print("c  =", c, "   4c^2P* <=", f_up(4 * c * c * Ps), "  P* <=", Ps, f"({time.time()-t:.1f}s)")
    # comparison with the d(n)^2 bound at Bellotti/Phase-0 parameters (row e^29, Phase-0 v2 optimum)
    for (L, u, v, w) in ((math.log(3e12), 2.5026650, 4.2690040, 0.71793831), (35.0, 2.0, 3.6, 0.55), (40.0, 1.8, 3.2, 0.48)):
        lVW = (v + w) * L
        D1 = 1 / math.pi ** 2
        D2 = D1 * lVW ** 3 + 0.746 * lVW ** 2 + 0.825 * lVW + 0.462 + D1 * lVW ** 4 / 4 + 0.746 * lVW ** 3 / 3 + 0.825 * lVW ** 2 / 2 + 0.462 * lVW
        print(f"L={L:.2f} u={u} v={v} w={w}:  K_D <= {f_up(KD_upper(u, v, w, L)):.4e}   vs  sum d^2/n ~ {D2:.4e}")
