"""Independent referee checks of Lemma D (review_round2).  Written from the mathematics, NOT from
phase2_lemmas/lemmaD_mollifier.py.  Floats / mpmath are used for brute force (exploration);
the constant c is additionally certified with exact rational/ball arithmetic (python-flint arb).

Checks
 1. Object: sum_n Psi(n)Theta(n) n^{-s} = zeta(s) * M(s),  M(s) = sum_{v<=V,w<=W} psi_v theta_w [v,w]^{-s}
    (Bellotti Lemma 3.4), tested at s = 2 and s = 1.5 (truncated n-sum, tail estimated).
 2. |M(1/2+it)| <= S_abs := sum |psi_v||theta_w| [v,w]^{-1/2} (max over a t-grid) -- trivial, sanity.
 3. S_abs <= Lemma-D bound 4 c^2 P* (V^1/2-U^1/2)(W^1/2-1)/(log(V/U) log W) for integer and non-integer U,V,W,
    and the intermediate bounds A_delta <= 2c(V^1/2-U^1/2)/(Delta delta), B_delta <= 2c(W^1/2-1)/(delta log W).
 4. c = sup_{y>0} Q(y)/sqrt(y) = Q(7)/sqrt(7): arb check for m <= 10^6 + own tail bound
    Q(y) <= (12/pi^2) sqrt(y) + 2 sqrt(y)/(floor(sqrt y)) - (12/pi^2)*0 ... (see REVIEW.md) ; also D.2 numerically.
 5. P* = prod_p (1 + p^{-3/2} - p^{-2}).
"""
import math, sys, time
import numpy as np
import mpmath as mp
from flint import arb, ctx

ctx.prec = 80


def mobius_sieve(N):
    mu = np.ones(N + 1, dtype=np.int64)
    is_comp = np.zeros(N + 1, dtype=bool)
    primes = []
    for i in range(2, N + 1):
        if not is_comp[i]:
            primes.append(i)
            mu[i::i] *= -1
            is_comp[2 * i::i] = True
            if i * i <= N:
                mu[i * i::i * i] = 0
    mu[0] = 0
    return mu, primes


def weights(U, V, W, mu):
    """psi_v (Bellotti (3.1)) for v<=V and theta_w for w<=W (U, V, W real)."""
    D = math.log(V / U); lW = math.log(W)
    psi = {}
    for v in range(1, int(math.floor(V)) + 1):
        if mu[v] == 0:
            continue
        if v <= U:
            psi[v] = float(mu[v])
        else:
            psi[v] = mu[v] * math.log(V / v) / D
    th = {}
    for w in range(1, int(math.floor(W)) + 1):
        if mu[w] == 0:
            continue
        th[w] = mu[w] * math.log(W / w) / lW
    return psi, th


def lcm(a, b):
    return a // math.gcd(a, b) * b


def check_object(U, V, W, mu, s, N=200000):
    psi, th = weights(U, V, W, mu)
    # M(s)
    Ms = mp.mpf(0)
    for v, pv in psi.items():
        for w, tw in th.items():
            Ms += pv * tw * mp.power(lcm(v, w), -s)
    # Dirichlet series sum_{n<=N} Psi(n)Theta(n) n^-s
    Psi = np.zeros(N + 1); The = np.zeros(N + 1)
    for v, pv in psi.items():
        Psi[v::v] += pv
    for w, tw in th.items():
        The[w::w] += tw
    n = np.arange(1, N + 1, dtype=float)
    DS = float(np.sum(Psi[1:] * The[1:] * n ** (-s)))
    return float(mp.zeta(s) * Ms), DS


def S_abs_and_parts(U, V, W, mu):
    psi, th = weights(U, V, W, mu)
    vs = np.array(list(psi.keys())); pv = np.abs(np.array(list(psi.values())))
    S = 0.0
    for w, tw in th.items():
        if tw == 0:
            continue
        g = np.gcd(vs, w)
        L = vs // g * w
        S += abs(tw) * float(np.sum(pv * L.astype(float) ** -0.5))
    return S, psi, th


def maxM_half(psi, th, ts):
    pairs = {}
    for v, pv in psi.items():
        for w, tw in th.items():
            n = lcm(v, w)
            pairs[n] = pairs.get(n, 0.0) + pv * tw
    ns = np.array(list(pairs.keys()), dtype=float); cs = np.array(list(pairs.values()))
    best = 0.0
    for t in ts:
        val = np.sum(cs * ns ** -0.5 * np.exp(-1j * t * np.log(ns)))
        best = max(best, abs(val))
    return best, abs(np.sum(cs * ns ** -0.5))


def certify_c_own(Y1=10 ** 6):
    mu, _ = mobius_sieve(Y1)
    sq = np.sqrt(np.arange(1, Y1 + 1, dtype=float))
    Qf = np.cumsum(np.where(mu[1:] != 0, 1.0 / sq, 0.0))
    ratio = Qf / sq
    m_star = int(np.argmax(ratio)) + 1
    second = np.sort(ratio)[-2]
    # rigorous: Q(7)/sqrt7 as an arb ball; the float ratio array has relative error <~ 1e-10, far below the gap
    Q7 = sum(1 / arb(m).sqrt() for m in (1, 2, 3, 5, 6, 7))
    c7 = Q7 / arb(7).sqrt()
    gap = float(c7.lower()) - second
    return m_star, c7, second, gap, Qf


def own_tail_bound(y):
    """Referee's elementary bound (proved in REVIEW.md):  Q(y) <= (12/pi^2) sqrt(y) + 2 sqrt(y)/floor(sqrt(y))
    + 2 (1 + log sqrt(y)),  valid for y >= 1."""
    D = math.floor(math.sqrt(y))
    return 12 / math.pi ** 2 * math.sqrt(y) + 2 * math.sqrt(y) / D + 2 * (1 + 0.5 * math.log(y))


def Pstar(P=10 ** 7):
    _, primes = mobius_sieve(P) if P <= 10 ** 6 else (None, None)
    if primes is None:
        # simple numpy prime sieve
        s = np.ones(P + 1, dtype=bool); s[:2] = False
        for i in range(2, int(P ** 0.5) + 1):
            if s[i]:
                s[i * i::i] = False
        primes = np.nonzero(s)[0].astype(float)
    p = np.array(primes, dtype=float)
    lp = np.sum(np.log1p(p ** -1.5 - p ** -2))
    return math.exp(lp), math.exp(lp + 2 / math.sqrt(P))


if __name__ == "__main__":
    t0 = time.time()
    mu, _ = mobius_sieve(400000)
    print("== 1. object M(s): zeta(s) M(s) vs sum_n Psi Theta n^-s (n<=2e5) ==")
    for (U, V, W) in ((3.5, 40.2, 6.3), (10, 120, 15)):
        for s in (2.0, 1.5):
            a, b = check_object(U, V, W, mu, s)
            print(f"  U={U} V={V} W={W} s={s}:  zeta*M={a:.10f}  DS={b:.10f}  diff={a-b:.2e}")
    print("== 2/3. S_abs vs bound;  max_t |M(1/2+it)| <= S_abs ==")
    c_val = 1.3296349; P_val = 1.47523
    K = 4 * c_val ** 2 * P_val
    cases = [(1, 50, 7), (2.7, 333.3, 12.5), (10, 300, 20), (30, 3000, 50), (100, 20000, 100), (5, 20000, 400),
             (1.0, 7.5, 7.5), (1, 8, 1.5), (60, 20000, 1000), (1000, 100000, 50), (7, 7.01, 7)]
    for (U, V, W) in cases:
        S, psi, th = S_abs_and_parts(U, V, W, mu)
        bnd = K * (math.sqrt(V) - math.sqrt(U)) * (math.sqrt(W) - 1) / (math.log(V / U) * math.log(W))
        line = f"  U={U} V={V} W={W}:  S_abs={S:.5f}  bound={bnd:.5f}  ratio={bnd/S:.3f}"
        if len(psi) * len(th) < 4e5:
            mx, at0 = maxM_half(psi, th, np.linspace(0, 200, 2001))
            line += f"   max|M(1/2+it)| (t-grid)={mx:.4f}  |M(1/2)|={at0:.4f}"
        print(line, flush=True)
        assert bnd >= S
    print("== intermediate A_delta, B_delta bounds (U,V,W)=(10,3000,200) ==")
    U, V, W = 10, 3000, 200
    psi, th = weights(U, V, W, mu)
    D = math.log(V / U)
    worstA = 0; worstB = 0
    for d in range(1, 200):
        if mu[d] == 0:
            continue
        A = sum(abs(p) / math.sqrt(v) for v, p in psi.items() if v % d == 0)
        B = sum(abs(t) / math.sqrt(w) for w, t in th.items() if w % d == 0)
        worstA = max(worstA, A / (2 * c_val * (math.sqrt(V) - math.sqrt(U)) / (D * d)))
        worstB = max(worstB, B / (2 * c_val * (math.sqrt(W) - 1) / (d * math.log(W))))
    print(f"  max A_d/bound = {worstA:.4f}, max B_d/bound = {worstB:.4f} (must be <= 1)")
    print("== 4. c ==")
    m_star, c7, second, gap, Qf = certify_c_own()
    print(f"  argmax_m<=1e6 Q(m)/sqrt m = {m_star};  c = Q(7)/sqrt7 in {c7};  second best = {second:.10f}; gap {gap:.3e}")
    ys = np.arange(1, 10 ** 6 + 1, dtype=float)
    D2 = 12 / math.pi ** 2 * np.sqrt(ys) + 1.5 * np.log(ys) + 2.4
    print(f"  D.2 (12/pi^2)sqrt y + 1.5 log y + 2.4 >= Q(m) for all m<=1e6: {bool(np.all(D2 >= Qf))};"
          f" min slack {float(np.min(D2 - Qf)):.4f} at m={int(np.argmin(D2 - Qf))+1}")
    own = np.array([own_tail_bound(y) for y in ys[::997]])
    print(f"  referee's bound >= Q on sample: {bool(np.all(own >= Qf[::997]))};  bound/sqrt(y) at 1e6: {own_tail_bound(1e6)/1e3:.5f}")
    print("== 5. P* ==")
    p_lo, p_hi = Pstar()
    print(f"  prod_{{p<=1e7}} = {p_lo:.7f};  with tail factor exp(2/sqrt(1e7)): {p_hi:.7f}")
    print(f"  4 c^2 P* <= {4 * float(c7.upper())**2 * p_hi:.5f}")
    print(f"done {time.time()-t0:.0f}s")
