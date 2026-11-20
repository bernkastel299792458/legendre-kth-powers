# A Gaussian piece with the exact least common multiple

In the [two-index Gaussian estimate](BILINEAR_BAND.md), replace \(de\) by \([d,e]\). This change includes the true greatest common divisor for every pair. Denote the resulting finite sum by \(S_*\); again \(z=\sqrt2X\). The following are strict upper bounds on \(|S_*|/X^2\) for every real \(|\kappa|\) up to the displayed endpoint.

| \(\log X\) | upper \(\log|\kappa|\) | \(g_0,R\) | bound |
|---:|---:|---|---:|
| 55 | 15 | \(1024,32768\) | .000161024 |
| 60 | 16 | \(1024,32768\) | .000001524 |
| 70 | 16 | \(1024,32768\) | \(5.710\cdot10^{-8}\) |

Fix the true gcd \(g\), insert \(\sum_{h\mid(d/g,e/g)}\mu(h)\), and put \(m=gh\). The phase in the resulting sum on multiples of \(m\) has parameter \(g\kappa\) and product denominator \(de\). For \(m\) squarefree and \(d=mr\) in the top half of the sieve, the coefficient \(G_*\lambda_{mr}\) is \(\mu(m)(m/\varphi(m))\mu(r)r/\varphi(r)\) if \((m,r)=1\), and zero otherwise. For nonsquarefree \(m\) all terms vanish. Split out the Euler product of \(1/\zeta(s)\) as in the [single-band proof](SELBERG_BAND.md); primes dividing \(m\) supply \((1-p^{-s})^{-1}\) and the remaining primes have the previous extra product majorant. At \(X'=X/m\) the contour bounds with the original \(X\), normalized by \(X'\), can therefore be multiplied by \(F(m)m^{1-\sigma}\), where \(F(m)=(m/\varphi(m))\prod_{p\mid m}(1-p^{-\sigma})^{-1}\). Use the unchanged denominator \(G_*\ge\log z+1.331\). The tails of the Gaussian outside the matching interval obey the single-band estimate with \(X'\ge X/R\) in the discrete maximum and \(\log(mr)\le\log X+r/X'\). Call this additional bound \(\epsilon\). Thus both twisted sums on multiples of \(m\), now divided by \(X\), cost at most \((U+\epsilon)F(m)/m^\sigma\) in the finite frequency window. Here \(U\) is the single-band normalized bound at \(X\), uniform throughout \(|\tau|\le e^{27}\).

Let \(J\) be the Fourier mass bound in the two-index proof at the maximal \(|\kappa|\); the bound at \(g|\kappa|\) is at most \(\sqrt g J\). Use \(F(gh)\le F(g)F(h)\) on the nonzero terms. Then the low Fourier part over \(g\le g_0,\ gh\le R\) costs at most
\[
 J(U+\epsilon)^2
 \left(\sum_{g\le g_0}\mu^2(g)\sqrt g\,F(g)^2g^{-2\sigma}\right)
 \left(\sum_{h\le R}\mu^2(h)F(h)^2h^{-2\sigma}\right).
\]
Use the order-16 Fourier tail established in the two-index proof at \(g_0|\kappa|\). In this tail the unrestricted single-multiple Gaussian bound is at most \(c_\omega/m+1/X\), where \(c_w=\sqrt{2\pi}w e^{w^2/2}\). Summing its square costs at most \((c_\omega+R/X)^2\zeta(2)^2\).

For the remaining gcd and inversion tails, a uniform majorant for the original sum of absolute weights on multiples of \(m\), divided by \(X\), is \(B/m+D/X\). Indeed in the true top dyadic band \(|\lambda_d|\le b=\max_{d\le z}(d/\varphi(d))/(\log z+1.331)\), bounded by an initial primorial. Outside it, replace \(W_\delta\) by \(e^{-(\log2)^2/(16\delta^2)}W_{\sqrt2\delta}\), and use \(|\lambda_d|\le1\). This gives the explicit \(B,D\) in the program. For \(g>g_0\) remove the coprimality restriction directly. For \(g\le g_0\) and \(gh>R\) sum the absolute squares on multiples of \(gh\). Use \(R\ge2g_0\), \(\sum_{h>R/g}h^{-2}\le2g/R\), \(\sum_{g\le g_0}1/g\le Q=1+\log g_0\), and \(m\le z\) on every nonempty sum. The two tails together are bounded by
\[
 B^2(1/g_0+2Q/R)+
 2BD(1+\log z)(1+Q)/X+D^2z(1+Q)/X^2 .
\]
All estimates increase with the maximal allowed \(|\kappa|\), and conjugacy handles the other sign. The remaining full physical-sieve problem includes different block locations and lengths, and all real frequencies in its kernel.

~~~sh
python -B round7/mobius/lcm_band.py
~~~
