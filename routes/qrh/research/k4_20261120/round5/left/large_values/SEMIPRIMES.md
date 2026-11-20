# Extending a short detector with a prime block

Fix \(T=e^{35},s=.85\). The following calculation tests the signed detector of [GAUSSIAN.md](GAUSSIAN.md). With \(N=2^j<B\), replace the critical polynomial by
\[
 P(s)=E_6(s)\left[\sum_{n\le N,(n,6)=1}\frac{\mu(n)}{n^s}
  -E_F(s)\sum_{N<p\le B}\frac1{p^s}\right],
 \qquad E_F(s)=\prod_{\ell\mid F}(1-\ell^{-s}).
\]
Here \(F=1,5,35\). The finite Möbius head is unchanged. For each prime \(N<p\le B\), the coefficient of \(\zeta P\) is zero. The coefficient at each prime \(p>B\) is one.

## A joint critical second moment

For \(F=1\), [prime_mollifier.py](prime_mollifier.py) computes the mixed second moment directly with the combined coefficients, retaining their arithmetic cross terms. The squarefree core consists of the original coprime set and the extra primes, all of whose signs are \(-1\). All divisors of a core index are themselves in the core, and a new prime has divisors \(1,p\). Thus the gcd-prefix identities and all error bounds of [FAST_SHORT.md](../FAST_SHORT.md) apply unchanged. Physical indices are formed by merging four increasing lists \(rn,\ r=1,2,3,6\); uniqueness follows from coprimality. The new primes are sieved by removing all multiples of every integer through \(\sqrt B\) starting at its square or the first permissible multiple above \(N\). The exact integer range and the binary64 accumulated error bounds are checked. The counts, weighted sums and squared Dirichlet convolution are for the full *combined* set. The averaged harmonic remainder still uses the factor \(\prod_{p\mid6}(1+2/(p(p+1)))\) since \(r\mid6\) is independent of \(n\).

| \(N\) | \(B\) | Additional primes | Certified joint second coefficient \(S(35)\) | Type II fraction, \(\theta=.35,Y=512T\) |
|---:|---:|---:|---:|---:|
| \(2^{20}\) | \(2^{25}\) | 1,981,664 | <3.7060 | <.13622 |
| \(2^{20}\) | \(2^{26}\) | 3,875,784 | <7.7654 | <.28543 |
| \(2^{22}\) | \(2^{26}\) | 3,661,862 | <10.3011 | <.37864 |

The Gaussian fractions use the simple matched reflected Poisson bound \(3/[2(c-\tfrac12)]\), as in [RIESZ.md](RIESZ.md). At these parameters \(\Phi\) differs negligibly from one in all of the first \(B\) Dirichlet coefficients. Accounting for Type II leaves a signed detection threshold slightly below .65. A cutoff .25 instead gives an available signed threshold slightly below .75.

## Mixed semiprime coefficients

Let \(\ell\) be a small prime dividing neither 6 nor \(F\), and let \(p>\ell\) be a second prime. Whenever \(N<\ell p\le B\), the coefficient of \(\zeta P\) at \(\ell p\) is exactly \(-1\). If \(p\le N\), the initial convolution contributes \(1-1-1\), while the prime block contributes nothing. If \(p>N\), the initial convolution gives \(1-1=0\) and the new large-prime divisor contributes \(-1\). This argument also works for any finite correcting cofactor whose coefficient at \(\ell\) vanishes and whose constant coefficient is one.

For each \(F\) choose a set \(\mathcal L\) of allowable small primes with \(2\max\mathcal L<(\min\mathcal L)^2\).
The test uses all primes \(5\le\ell\le11\), \(7\le\ell\le23\), or \(11\le\ell\le59\) for \(F=1,5,35\), respectively. In each block \(m<n\le2m\) with \(N\le m<B\), retain all \(n=\ell p,\ \ell\in\mathcal L\). Our parameters satisfy \((\max\mathcal L)^2<m/2\). Any factorization of a product of \(k\) such terms into \(k\) block indices must put exactly one large prime in each index: two would exceed \(2m\). Two small factors alongside that large prime likewise exceed \(2m\), since the large prime exceeds \(m/\max\mathcal L\). Each index must therefore contain one small and one large prime. Every permissible term contributing to any such product coefficient has the same sign \((-1)^k\). This remains true when different small primes are exchanged between the factors. Contributions cannot cancel.

Thus the [previous power norm and distinct-tuple floor](GAUSSIAN.md) applies with \(g\) from *all* these mixed semiprimes in the block. They are disjointly enumerated by their small prime. Each block is split into 16 subintervals \((l,r]\) and the contribution from small prime \(\ell\) is bounded below by \(.999^2 r^{-2\Theta}[\pi(r/\ell)-\pi(l/\ell)]\), evaluated by a sieve. This Gaussian bound holds through \(2^{27}\) at \(Y\ge128e^{35}\). For \(m\ge B\) the prime-only floor remains valid. Enforce the global block count fraction constraint by exactly the same finite dual multipliers and all positive integer powers as before.

| \(N\) | \(B\) | \(F=1\) | \(F=5\) | \(F=35\) |
|---:|---:|---:|---:|---:|
| \(2^{20}\) | \(2^{25}\) | >.93677 | >.95142 | >.97316 |
| \(2^{20}\) | \(2^{26}\) | >.91606 | >.93347 | >.95922 |
| \(2^{21}\) | \(2^{26}\) | >.85013 | >.86378 | >.88396 |
| \(2^{22}\) | \(2^{26}\) | >.79399 | >.80431 | >.81987 |
| \(2^{20}\) | \(2^{27}\) | >.92180 | >.94208 | >.97216 |

These are necessary total amplitudes for the two optimistic independent-block estimates, giving Type I the entire original \(R=7(\log T)T^{p_s}\) even before paying for Type II. The certificate therefore excludes the usual .65 and .75 splits in these examples. Different columns use different semiprime subfamilies, so their order has no implication about which of the true detectors is better. The result leaves open joint estimates using the signed sums across blocks.

Run **python -B prime_mollifier.py --n 20 --b 26** for the second row and **python -B semiprime_floor.py** for the semiprime table. Codex derived these estimates under the Claude/Codex research attribution protocol.
