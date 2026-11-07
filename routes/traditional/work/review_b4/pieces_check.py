"""
pieces_check.py -- numerical check (float64; sanity only, NOT a proof) of every inequality in
the proof of Theorem R at a moderate real X, for several eps.  Written from scratch.

For each squarefree l <= X, Y = X/l:
   m1 = m_l(Y) = sum_{n<=Y,(n,l)=1} mu(n)/n,   ms = m_l(Y;1+eps),
   P_l = prod_{p|l} (1-p^{-s})^{-1},  Delta_l = (ms Y^eps - m1 - P_l Y^eps/zeta)/eps   (RZA Lemma 3.1 def.)
   w_l = phi_s(l) X^{-2eps}/l^2,  b_l = phi(l)/l^2.
Checks:
  (R.1)  S_eps(X) = sum w (m1+eps Delta)^2 + 2/zeta - G(X)/zeta^2 ;  RZA (6.6) RHS (b_l X^{-2eps} instead of w)
  R1(a), R1(b) termwise;
  A1 sqrt-part |Delta| <= (4.1 g0 + a_eps) sqrt(l)/phi_{1/2}(l) 2^eps / sqrt(Y)   (no log part: Y < 1e10)
  sign table: Delta <= 0 for Y<10.9 ; eps Delta Y^-eps >= -P/zeta ; m Delta <= (19/210)|Delta| for 10.9<=Y<47
  Step 3 sums vs 2 eps X^-eps ax1 and (G(X)-G(X/10.9))/zeta^2 ; Step 4 sum vs T4 ; Step 5 sum vs T6 (sqrt part)
  Step 7: tail sum vs (J+0.9999)^{-2eps} * sum_{l<=D} b m^2 and RZA Lemma 5.1 bound; bulk vs Hoelder bound.
Usage: python -I pieces_check.py X eps1,eps2,...
"""
import sys, math, time
import numpy as np
import mpmath as mp

TH = dict(TH1=2.1205286, THx1=6.2404074, THx2=3.1885613, THx=1.8222265, THxxx=2.5878076,
          L1=0.13779107, L2=0.09686390, H1=0.010032)


def sieve(n):
    isp = np.ones(n + 1, dtype=bool); isp[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if isp[i]:
            isp[i * i::i] = False
    P = np.nonzero(isp)[0]
    mu = np.ones(n + 1, dtype=np.int64); mu[0] = 0
    for p in P:
        mu[p::p] *= -1
        if p * p <= n:
            mu[p * p::p * p] = 0
    return P, mu


def mult(n, P, mu, fp):
    g = np.ones(n + 1)
    for p in P:
        g[p::p] *= fp(float(p))
    g[mu == 0] = 0.0
    return g


def run(X, epss, e0=0.0227, J=68):
    n = int(math.floor(X))
    P, mu = sieve(n)
    sq = np.nonzero(mu)[0]
    nn = np.arange(n + 1, dtype=np.float64); nn[0] = 1
    x1 = mu / nn
    b = mult(n, P, mu, lambda p: (p - 1)) / nn ** 2
    g0 = mult(n, P, mu, lambda p: (math.sqrt(3) * (math.sqrt(2) - 1) / 2 if p == 2 else 1.0))
    phihalf = mult(n, P, mu, lambda p: math.sqrt(p) - 1)
    h = mult(n, P, mu, lambda p: p ** (1 / (p - 1)))
    ks = len(epss)
    S = np.array([1 + e for e in epss])
    xs = np.stack([mu * nn ** (-s) for s in S], axis=1)
    m1 = np.zeros(n + 1); ms = np.zeros((n + 1, ks))
    t0 = time.time()
    for l in sq.tolist():
        Yi = int(math.floor(X / l))
        idx = np.arange(1, Yi + 1)
        cop = np.gcd(idx, l) == 1
        m1[l] = x1[1:Yi + 1][cop].sum()
        ms[l] = xs[1:Yi + 1][cop].sum(axis=0)
    print("X=%s: m-sums done (%.1f s), %d squarefree l" % (X, time.time() - t0, len(sq)), flush=True)
    l = sq.astype(np.float64)
    Y = X / l
    bad = 0
    def chk(cond, msg):
        nonlocal bad
        print(("   OK   " if cond else "   FAIL ") + msg)
        bad += 0 if cond else 1
    for k, e in enumerate(epss):
        s = 1 + e
        zeta = float(mp.zeta(s))
        Pinv = mult(n, P, mu, lambda p: 1 - p ** (-s))
        Pl = 1 / Pinv[sq]
        phis = l ** s * Pinv[sq]
        Ye = Y ** e
        D = (ms[sq, k] * Ye - m1[sq] - Pl * Ye / zeta) / e
        w = phis * X ** (-2 * e) / l ** 2
        bl = b[sq]
        G = np.sum(1 / phis)
        S_classic = np.sum(phis * l ** (-2 * s) * ms[sq, k] ** 2)
        S_R1 = np.sum(w * (m1[sq] + e * D) ** 2) + 2 / zeta - G / zeta ** 2
        S_66 = X ** (-2 * e) * np.sum(bl * (m1[sq] + e * D) ** 2) + 2 / zeta - G / zeta ** 2
        print(" eps=%g  zeta=%.6f  S_eps(X) classic=%.10f  via (R.1)=%.10f  RZA(6.6) RHS=%.10f" % (e, zeta, S_classic, S_R1, S_66))
        chk(abs(S_classic - S_R1) < 1e-9, "(R.1) identity reproduces S_eps(X)")
        chk(S_66 < S_classic, "RZA (6.6) RHS < S_eps(X), i.e. (6.6) false here (expected)")
        chk(np.all(w <= bl * (l / X) ** (2 * e) * (1 + 1e-12)), "R1(a) w <= b (l/X)^{2eps} for all l")
        chk(np.all(w <= X ** (-e) * bl * h[sq] ** e * (l / X) ** e * (1 + 1e-12)), "R1(b) w <= X^-eps b h^eps (l/X)^eps for all l")
        a = (5 + e * 2 ** e) / 2
        sqp = np.sqrt(l) / phihalf[sq]
        A1 = (4.1 * g0[sq] + a) * sqp * 2 ** e / np.sqrt(Y)
        r = np.abs(D) / A1
        chk(np.all(r <= 1), "A1 sqrt-part bound on |Delta| (max ratio %.4f, at Y>=1e3: %.4f)" % (r.max(), r[Y >= 1e3].max()))
        big = Y < 10.9
        chk(np.all(D[big] <= 1e-12), "Delta <= 0 for Y < 10.9 (max %.3e)" % D[big].max())
        chk(np.all(e * D[big] / Ye[big] >= -Pl[big] / zeta - 1e-12), "eps Delta Y^-eps >= -P/zeta for Y < 10.9")
        mid = (Y >= 10.9) & (Y < 47)
        chk(np.all(m1[sq][mid] * D[mid] <= 19 / 210 * np.abs(D[mid]) + 1e-12), "m Delta <= (19/210)|Delta| on 10.9<=Y<47")
        cross_big = np.sum(2 * e * w[big] * m1[sq][big] * D[big])
        ax1 = (6 / math.pi ** 2 * math.log(10.9 / 5) + 0.008) / 30
        chk(cross_big <= 2 * e * X ** (-e) * ax1, "Step 3 cross: %.3e <= 2eps X^-eps ax1 = %.3e" % (cross_big, 2 * e * X ** (-e) * ax1))
        sq_big = np.sum(e * e * w[big] * D[big] ** 2)
        Gb = np.sum(1 / phis[big])
        chk(sq_big <= Gb / zeta ** 2 + 1e-14, "Step 3 square: %.6e <= (G(X)-G(X/10.9))/zeta^2 = %.6e" % (sq_big, Gb / zeta ** 2))
        small = ~big
        cross_small = np.sum(2 * e * w[small] * m1[sq][small] * D[small])
        ax2 = 19 / 210
        T4 = 2 * e * 2 ** e * (4.1 * TH["THx"] + a * TH["THxxx"]) * (10.9 ** (-2 * e) * ax2 / math.sqrt(10.9) + 47 ** (-2 * e) * (1 - ax2) / math.sqrt(47))
        chk(cross_small <= T4, "Step 4 cross (l<=X/10.9): %.4e <= T4 = %.4e" % (cross_small, T4))
        sq_small = np.sum(e * e * w[small] * D[small] ** 2)
        Q = (a * a * TH["THx1"] + 8.2 * a * TH["THx2"] + 4.1 ** 2 * TH["TH1"]) / 10.9
        T6s = e * e * 10.9 ** (-2 * e) * 2 ** (2 * e) * Q
        chk(sq_small <= T6s, "Step 5 square (sqrt part only): %.4e <= %.4e" % (sq_small, T6s))
        # main term
        Z = J + 0.9999
        Dd = X / Z
        tl = l <= Dd
        Mt = np.sum(w[tl] * m1[sq][tl] ** 2)
        S0ss = np.sum(bl[tl] * m1[sq][tl] ** 2)
        Tail0 = 2 * TH["TH1"] / Z + 2 * math.sqrt(2) * TH["H1"] * TH["L1"] / math.sqrt(Z) + TH["H1"] ** 2 * TH["L2"]
        chk(Mt <= Z ** (-2 * e) * S0ss and S0ss <= Tail0, "Step 7 tail: %.6f <= Z^-2eps * %.6f, and S0**=%.6f <= Tail0(Lemma 5.1)=%.6f" % (Mt, S0ss, S0ss, Tail0))
        bu = ~tl
        Mb = np.sum(w[bu] * m1[sq][bu] ** 2)
        B0 = np.sum(bl[bu] * m1[sq][bu] ** 2)
        B1 = np.sum(bl[bu] * h[sq][bu] ** e0 * m1[sq][bu] ** 2)
        t = e / e0
        hb = X ** (-e) * B0 ** (1 - t) * B1 ** t
        chk(Mb <= hb, "Step 7 bulk: %.6f <= X^-eps B0^(1-t) B1^t = %.6f  (B0=%.6f, B1=%.6f)" % (Mb, hb, B0, B1))
        print("   pieces: M=%.6f cross_big=%.2e cross_small=%.2e sq=%.2e  2/z-G(X/10.9)/z^2=%.6f" % (
            Mt + Mb, cross_big, cross_small, sq_big + sq_small, 2 / zeta - (G - Gb) / zeta ** 2))
    return bad


if __name__ == "__main__":
    X = float(sys.argv[1]) if len(sys.argv) > 1 else 1e6 + 0.5
    epss = [float(t) for t in sys.argv[2].split(",")] if len(sys.argv) > 2 else [1e-3, 0.01, 0.0227]
    bad = run(X, epss)
    print("DONE, %d FAIL" % bad)
