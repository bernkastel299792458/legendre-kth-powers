# Float sanity check (NOT a proof) of F_1(x) = sum_{n<=x,(n,q)=1} mu(n)/n log(x/n) >= 0
# (RZ23 Lemma 4.1 = Ramare, Math. Comp. 84 (2015), Cor. 1.10), for q in {1,2,3,6,30,210}, x <= 1e7.
# F_1 is continuous and linear in log x on [N,N+1], so it suffices to look at integers N.
#   F_1(N) = m_q(N) log N - sum_{n<=N} mu(n) log(n)/n.
import numpy as np
XMAX = 10**7
mu = np.ones(XMAX + 1, dtype=np.int8); mu[0] = 0
isp = np.ones(XMAX + 1, dtype=bool); isp[:2] = False
for p in range(2, XMAX + 1):
    if isp[p]:
        isp[2 * p::p] = False
        mu[p::p] *= -1
        if p * p <= XMAX: mu[p * p::p * p] = 0
n = np.arange(XMAX + 1, dtype=np.float64); n[0] = 1
for q in [1, 2, 3, 6, 30, 210]:
    w = mu.astype(np.float64) / n; w[0] = 0
    for p in [2, 3, 5, 7]:
        if q % p == 0: w[::p] = 0
    m = np.cumsum(w); T = np.cumsum(w * np.log(n))
    F = m[1:] * np.log(n[1:]) - T[1:]
    qphi = np.prod([p / (p - 1) for p in [2, 3, 5, 7] if q % p == 0]) if q > 1 else 1.0
    i = int(np.argmin(F[1:])) + 1
    big = F[10**5 - 1:]
    print('q=%-4d min_{2<=N<=1e7} F_1(N) = %.6g at N=%d ; min over N>=1e5: %.6g ; max F_1/(q/phi(q)) = %.6f' % (
        q, F[i], i + 1, big.min(), F.max() / qphi))
