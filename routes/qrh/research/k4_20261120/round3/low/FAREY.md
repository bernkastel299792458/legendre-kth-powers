# A long-interval prime sieve and the lower fourth-power range

For every real \(x\) with \(115.00099\le\log x\le115.032114\), there
is a prime in \((x,x+4x^{3/4})\). This connects to the earlier lower
range and gives all \(n\le3\,086\,406\,237\,318\). The inputs are
published results, including finite-height RH. Adding QRH(7/8) gives
\(\log x\le115.032116\), hence all \(n\le3\,086\,407\,780\,522\).
The new ingredient is the following explicit sieve inequality for all
\(x\ge0,\ y\ge e^{50}\):
\[
 \pi(x+y)-\pi(x)\le \frac{2y}{\log y+1.090}.                       \tag{1}
\]
The use of a long-interval estimate inside the signed Fourier kernel
was suggested by Yamada's Theorem 1. The derivation below uses the
published weighted large sieve and the published squarefree-totient
estimate. The local spacing argument supplies a separate \(0.1\) in
the denominator. The [Arb verifier](farey_sieve.py) also checks the
independent, coarser \(0.990\) version and its endpoint \(115.02925\).
[Yamada's preprint, equations (9)–(12)](https://arxiv.org/pdf/2312.16090v1).

## The weighted large sieve

Let \(N=\lceil y\rceil+1,\ z=\sqrt{N/C},\ C=4/3\). Let \(\mathcal S\)
be the primes \(p>z\) of the interval \((x,x+y]\), embedded in \(N\)
consecutive integers, and \(Z=\#\mathcal S\). For its exponential
sum \(S(\alpha)=\sum_{n\in\mathcal S}e^{2\pi i n\alpha}\), write
\(\delta(\alpha)\) for the circular distance to the nearest other reduced
Farey fraction of denominator at most \(z\), including \(0/1\). The
weighted large sieve gives
\[
 \sum_\alpha \frac{|S(\alpha)|^2}{N+C/\delta(\alpha)}\le Z.          \tag{2}
\]
We use Preissmann's Hilbert constant \(4/3\) with the implication from
his inequality (D) to (B). Montgomery and Vaughan's Corollary 1
corresponds to replacing \(\delta(a/q)^{-1}\) by \(qz\) and taking
\(C=3/2\). [Preissmann, pp. 95–96, (B) and the theorem for (D)](https://www.e-periodica.ch/cntmng?pid=ens-001%3A1984%3A30%3A%3A30) · [Montgomery–Vaughan, (1.6)–(1.8)](https://doi.org/10.1112/S0025579300004708).

For squarefree \(q\le z\), every \(n\in\mathcal S\) is coprime to \(q\).
Its Ramanujan sum over the reduced residue classes of \(q\) is \(\mu(q)\),
by the divisor formula for that sum. Hence
\(\sum_{a\bmod q}^{*} S(a/q)=\mu(q)Z\). Apply weighted Cauchy–Schwarz
to this sum with the same denominators as (2). If \(M_q\) is the
average of \(\delta(a/q)^{-1}\) over the units, the contribution to
(2) of this \(q\) is at least \(Z^2/[\phi(q)(N+CM_q)]\). The case
\(q=1\) also satisfies the formula. For \(Z>0\), sum over squarefree
\(q\) and divide to obtain
\[
 Z\le N/\mathcal H,\qquad
 \mathcal H=\sum_{q\le z}\frac{\mu^2(q)}{\phi(q)(1+CM_q/N)}.       \tag{3}
\]
If \(Z=0\), the upper bound holds immediately.

## Denominators of the two neighbors

Always \(M_q\le qz\) since two distinct Farey fractions are separated
by at least the reciprocal of the product of their denominators.
For \(q\ge z/16\), we prove for every squarefree \(q\)
\[
 M_q\le q(z-.249q).                                                  \tag{4}
\]
For any \(a\bmod q\) coprime to \(q\), let \(s_+,s_-\) be the largest
positive integers at most \(z\) with \(as_\pm\equiv\pm1\bmod q\).
The two fractions of these denominators and determinant \(1\) with
\(a/q\) are its two neighbors. Indeed the denominator of any fraction
strictly between a determinant-one pair is at least the sum of the
two denominators, and \(q+s_\pm>z\). Thus
\(\delta(a/q)^{-1}=q\max(s_+,s_-)\).

For \(0\le v\le q/2\), each of \(s_+,s_-\) belongs to \((z-v,z]\)
for at most \(v\phi(q)/q+2^{\omega(q)}\) choices of \(a\). This is the
ordinary inclusion-exclusion bound for coprimes in a real interval,
since inversion and negation permute the units. Consequently the
fraction of \(a\)'s with \(\min(z-s_+,z-s_-)\ge v\) is at least
\((1-2v/q-2D_q)_+\), where \(D_q=2^{\omega(q)}/\phi(q)\).
Integrating gives mean deficit at least \(q(1-2D_q)^2/4\) when
\(D_q<1/2\). For squarefree \(q\),
\[
 \sqrt q\,D_q=\prod_{p\mid q}\frac{2\sqrt p}{p-1}\le\sqrt{30}.
\]
Only \(2,3,5\) have a factor exceeding 1. With
\(z_0=\sqrt{e^{50}/C}\), the certificate checks the lower bound
\((1-2\sqrt{30}/\sqrt{z_0/16})^2/4>.249\). This proves (4).

## Summing the sieve weights

Put \(G(t)=\sum_{q\le t}\mu^2(q)/\phi(q)\). Ramaré's Theorem 3.1 gives
\(G(t)=\log t+c_0+E(t)\), \(|E(t)|\le 2.44/\sqrt t\) for \(t>1\),
where \(1.33258<c_0<2\). The value at \(t=1\) makes no difference to
the following integrals. [Ramaré, Theorems 1.3 and 3.1](https://www.impan.pl/shop/en/publication/transaction/download/product/113104).

The baseline sum from \(M_q\le qz\) is
\[
 H_0=\sum_{q\le z}\frac{\mu^2(q)}{\phi(q)(1+q/z)}
       =\tfrac12 G(z)+z\int_1^z\frac{G(t)}{(z+t)^2}\,dt .
\]
The \(\log t+c_0\) part evaluates to
\(\log z-\log2+\log(1+1/z)+c_0z/(z+1)\). The endpoint error and
integral error together cost at most
\((1/2+2)\,2.44/\sqrt z\) since \(z/(z+t)^2\le1/z\).
In particular
\[
 2 H_0\ge\log N+2(1.33258)-\log(4C)-4/z_0-5(2.44)/\sqrt{z_0}.
                                                                    \tag{5}
\]
The numerical additive part exceeds \(0.9911347108\).

For \(u=q/z\in[1/16,1]\), using (4) adds at least
\[
 f(u)=\frac{.249u^2}{(1+u)(1+u-.249u^2)}
\]
to the baseline weight \(1/(1+u)\) in (3). This function is increasing:
it equals \(.249(u/(1+u))^2/[1-.249u^2/(1+u)]\), with increasing
numerator and decreasing positive denominator. Partition into cells
\((v,w]=(i/128,(i+1)/128]\), \(8\le i<128\), discarding the possible
leftmost endpoint. In each cell Ramaré bounds the squarefree mass
below by \(\log(w/v)-2.44[(z_0v)^{-1/2}+(z_0w)^{-1/2}]>0\).
Add twice the sum of these masses times \(f(v)\) to (5). This gives
\(2\mathcal H\ge\log N+1.0910575668\) uniformly over all \(N\ge e^{50}\).

To recover a real interval add at most \(z\le2\sqrt y\) for small
primes and use \(y\le N\le y+2\). For either \(\eta=.990\) from (5) or
\(\eta=1.090\) from (4)–(5), we have \(2\mathcal H\ge\log N+\eta+.001\).
The available \(.001\) absorbs the two losses because, writing \(u=\log y\),
\[
 2(u+2)e^{-u}+(u+2)^2e^{-u/2}<.001\qquad(u\ge50).
\]
Both functions decrease on this half-line. Multiplication by the
two positive denominators gives (1). This verifies the passage to
arbitrarily large \(y\).

## Transfer to fourth powers

Use the [signed finite-height proof and its tangent slopes](../../round2/local/EDGE.md)
with the new \(\eta\). Each tangent to \(2y/(\log y+\eta)\), at
\(Y=s e^c/K\), bounds the sieve expression for \(y\ge e^{50}\) by
concavity. For \(y<e^{50}\) the integer count is at most \(e^{50}+1\).
All tangents have positive slope and intercept exceeding this number.
Indeed the angular parameter satisfies \(2\pi-2a>2\) in every row;
all tangent scales, including the first of the 256 primary slabs, lie
between \(1/256\) and 7. Throughout \(115\le c<116,\ \log Y+\eta<120\).
Thus the intercept \(2Y/(\log Y+\eta)^2\) exceeds
\(2e^{115}/[256(H+300000)120^2]>e^{50}+1\), with
\(H=3\,000\,175\,332\,800\). Closed arithmetic intervals follow by
expanding their endpoints and taking a limit. The earlier proof handles
both endpoints of the desired open prime interval.

The verifier applies the existing budget on the adjacent closed cells
\([115.00099,115.03185]\), \([115.03185,115.03210]\),
\([115.03210,115.032114]\) with \(K-H=-1\,280\,000\), then on
\([115.032114,115.032116]\) with \(K-H=300\,000\) and QRH. The
largest of the four resulting normalized errors is below \(0.999999720\).
The integer endpoints are obtained by outward-rounded exponentiation
and checked on both sides by logarithms. The conservative \(0.990\)
route covers two cells through \(115.02925\) without (4). The connection
at \(115.00099\) uses the old chain of published results.

Reproduce from this directory with Python and python-flint:

~~~text
python -B farey_sieve.py
~~~

This is a written argument with 192-bit Arb checks of its numerical
inequalities. Larger \(L\) in the middle interval remain open. Project
attribution to Claude and Codex. Codex developed this sieve estimate
and its numerical transfer in the QRH workstream.
