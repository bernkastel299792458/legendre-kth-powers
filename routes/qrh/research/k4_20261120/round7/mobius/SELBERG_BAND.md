# A Gaussian estimate for the signed Selberg coefficients

Put \(X=e^x,\ z=\sqrt2X,\ \omega=1/32,\ W_\omega(v)=\exp(-v^2/(2\omega^2))\). Let \(\lambda_d\) be the exact coefficients in the [physical sieve](../physical/BILINEAR.md), extended by zero above \(z\), and write \(G_*=G(z)\). Then for \(z/2<d\le z\) the factor \(G_d(z/d)\) equals 1 and \(G_*\lambda_d=\mu(d)d/\varphi(d)\). This gives a bound for the actual polynomial \(\sum_d\lambda_d W_\omega(\log(d/X))d^{-i\tau}\).

Indeed the infinite replacement has Dirichlet series
\[
 \sum_{d\ge1}\frac{\mu(d)d}{\varphi(d)d^s}
 =\frac1{\zeta(s)}\prod_p\left(1-\frac{p^{-s}}{(p-1)(1-p^{-s})}\right).
\]
The added product converges absolutely for \(\sigma=\Re s>0\). For \(p\le P=500\) take each absolute majorant, and for the tail bound the logarithm by \(P^{-\sigma}/[\sigma(1-1/P)(1-P^{-\sigma})]\), by comparison with the integral of \(t^{-1-\sigma}\). Thus the [finite contour and high-ordinate estimate](POISSON_POWERS.md) apply with the product majorant on each side. The contour uses height \(B=3000\).

Write \(h=(\log2)/2\). Off the matching dyadic block, the error at each \(d\) is at most \(G_*+2(1+\log d)\). To see the second term, expand \(d/\varphi(d)=\sum_{k\mid d}\mu^2(k)/\varphi(k)\), then expand \(1/\varphi(k)\) in the same way after factoring out \(1/k\). The resulting sum is bounded by \((1+\log d)\prod_p(1+1/[p(p-1)])<2(1+\log d)\). This last product is less than 2 by multiplying the primes through 500 and bounding the logarithmic tail by \(1/500\). Use the explicit bounds \(\log z+1.331\le G_*\le\log z+3\) from the same sieve proof. The off-block Gaussian is at most \(e^{-h^2/(4\omega^2)}W_{\sqrt2\omega}\). Using \(\log d\le\log X+d/X\), the two needed discrete sums of \((d/X)^j W_{\sqrt2\omega}(\log(d/X))\), divided by \(X\), are bounded by
\[
2\sqrt\pi\,\omega e^{((j+1)\omega)^2}+X^{-1}e^{(j\omega)^2}\qquad(j=0,1).
\]
Each nonnegative summand as a function of the continuous variable is unimodal, so the sum costs its integral plus its maximum. This proves the stated full-polynomial estimate after adding the leakage and dividing by the lower bound for \(G_*\).

| \(x\) | \(\log|\tau|\) | Bound divided by \(X\) |
|---:|---:|---:|
| 43 | 26 | .000152986 |
| 55 | 15 | \(1.87876\cdot10^{-7}\) |
| 60 | 25 | \(1.57519\cdot10^{-7}\) |
| 70 | 25 | \(2.49856\cdot10^{-9}\) |

~~~sh
python -B round7/mobius/selberg_band.py
~~~
