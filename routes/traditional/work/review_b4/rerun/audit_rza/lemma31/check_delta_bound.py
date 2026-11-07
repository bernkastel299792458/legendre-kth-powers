# Numerical sanity check (float64, NOT a proof) of the |Delta_q(X,eps)| bound of RZA Lemma 3.1
# and of the intermediate RZ23 bound (Thm 1.4 specialised, before inserting |m_q| bounds):
#   (I)  |Delta_q| <= (2^e/log2) X^-1 int_1^X |m_q(t)| dt + (1+2^{1/2+e}(1+e 2^{e-1} log2)) sqrt(q)/phi_{1/2}(q)/sqrt(X)
#   (L)  |Delta_q| <= 0.03 g2 q^xi/phi_xi 1_{X>=1e12}/log X + (4.1 g0 + (5+e2^e)/2) sqrt(q)/phi_{1/2}(q) 2^e/sqrt(X)
# Delta_q(X,e) = X^e (T(N) - P_q(e)/(e zeta(1+e))) + m_q(N) expm1(e log X)/e,  N=[X],
#   T(N) = sum_{l<=N,(l,q)=1} mu(l)/l * expm1(-e log l)/e     (no cancellation for small e)
# On [N,N+1) Delta is monotone in X^e, so we test both endpoints X=N and X=(N+1)^-.
import numpy as np
from scipy.special import zeta
import sys

XMAX = 10**7
def mobius_sieve(n):
    mu = np.ones(n + 1, dtype=np.int8); mu[0] = 0
    isp = np.ones(n + 1, dtype=bool); isp[:2] = False
    for p in range(2, n + 1):
        if isp[p]:
            isp[2 * p::p] = False
            mu[p::p] *= -1
            if p * p <= n: mu[p * p::p * p] = 0
    return mu
mu = mobius_sieve(XMAX + 1)
l = np.arange(XMAX + 2, dtype=np.float64)
logl = np.log(np.maximum(l, 1))
print('sieve done', flush=True)

def phi_s_ratio(q, s):  # q^s/phi_s(q)
    r = 1.0
    for p in [2, 3, 5, 7, 11, 13]:
        if q % p == 0: r /= (1 - p ** (-s))
    return r
def g0(q): return (np.sqrt(6) - np.sqrt(3)) / 2 if q % 2 == 0 else 1.0

out = []
for q in [1, 2, 3, 6, 30]:
    cop = np.ones(XMAX + 2, dtype=bool); cop[0] = False
    for p in [2, 3, 5]:
        if q % p == 0: cop[::p] = False
    w = np.where(cop, mu, 0).astype(np.float64) / np.maximum(l, 1)
    w[0] = 0
    m = np.cumsum(w)            # m[N] = m_q(N)
    absm_int = np.concatenate([[0.0], np.cumsum(np.abs(m[1:-1]))])  # int_1^{N} |m_q| = sum_{n=1}^{N-1}|m(n)|  -> index N-1 ...
    # int_1^N |m_q(t)|dt = sum_{n=1}^{N-1} |m_q(n)| ; absm_int[k] = sum_{n=1}^{k} |m(n)|
    sq = phi_s_ratio(q, 0.5)    # sqrt(q)/phi_{1/2}(q)
    for e in [1e-4, 0.01, 0.04, 0.1]:
        P = 1.0
        for p in [2, 3, 5]:
            if q % p == 0: P /= (1 - p ** (-1 - e))
        Z = 1.0 / (e * zeta(1 + e))
        T = np.cumsum(w * np.expm1(-e * logl) / e)
        N = np.arange(1, XMAX, dtype=np.int64)
        worstL = (0, None); worstI = (0, None); maxabs = 0
        for X in (N.astype(np.float64), N.astype(np.float64) + 1 - 1e-9):
            lX = np.log(X)
            D = np.exp(e * lX) * (T[N] - P * Z) + m[N] * np.expm1(e * lX) / e
            BL = (4.1 * g0(q) + (5 + e * 2 ** e) / 2) * sq * 2 ** e / np.sqrt(N + 1.0)   # bound at right end (smaller)
            intm = absm_int[N - 1] + np.abs(m[N]) * (X - N)   # int_1^X |m_q|
            BI = 2 ** e / np.log(2) * intm / X + (1 + 2 ** (0.5 + e) * (1 + e * 2 ** (e - 1) * np.log(2))) * sq / np.sqrt(X)
            rL = np.abs(D) / BL; rI = np.abs(D) / BI
            iL = int(np.argmax(rL)); iI = int(np.argmax(rI))
            if rL[iL] > worstL[0]: worstL = (rL[iL], X[iL])
            if rI[iI] > worstI[0]: worstI = (rI[iI], X[iI])
            # also large-X behaviour: max ratio over X >= 1e5
            sel = N >= 10**5
            maxabs = max(maxabs, float(np.max(rL[sel])))
        line = 'q=%-3d eps=%-7g  max|D|/bound_L = %.4f at X=%.6g ; max|D|/bound_I = %.4f at X=%.6g ; max ratio_L for X>=1e5: %.4f' % (
            q, e, worstL[0], worstL[1], worstI[0], worstI[1], maxabs)
        print(line, flush=True); out.append(line)
print('all ratios < 1:', all(float(s.split('= ')[1].split()[0]) < 1 and float(s.split('= ')[2].split()[0]) < 1 for s in out))
