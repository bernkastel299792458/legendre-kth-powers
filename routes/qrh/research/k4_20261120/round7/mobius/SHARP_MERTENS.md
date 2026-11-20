# A sharp uniform estimate for the Mertens prefix

Let \(M(Y)=\sum_{n\le Y}\mu(n)\). For \(38\le x\le59\) integral the replay bounds \(\sup_{x\le\log Y\le66}|M(Y)|/Y\). Some upper bounds are \(1.460\cdot10^{-5}\) at 38, \(1.924\cdot10^{-6}\) at 43, \(1.125\cdot10^{-7}\) at 50, \(1.512\cdot10^{-8}\) at 55, and \(2.932\cdot10^{-9}\) at 59. The only zero-location input is the published finite-height verification. Powers of \(Y\) on the vertical and horizontal sides of the proof use opposite endpoints of each closed length cell.

Write \(w=e^{-\ell}\), \(B=24/w,\ s=.56,\ u=1.75\). Replace the indicator of \(n\le Y\) by \(\Phi(\log(Y/n)/w)\), with \(\Phi\) the standard normal distribution function. The absolute difference has a nonnegative monotone part on each side of \(Y\), so its sum over integers is at most its integral plus two. The integral is \(Y\,\mathbb E|e^{wZ}-1|=Y e^{w^2/2}\operatorname{erf}(w/\sqrt2)\). This also bounds weighted unsmoothing when each coefficient is multiplied by a phase. The smoothed Perron integral has integrand \(Y^z e^{w^2z^2/2}/(z\zeta(z))\) and measure \(dz/(2\pi i)\). Move its segment \(|\Im z|\le B\) from \(u\) to \(s\). The verified zero-free strip contains the rectangle. Its two connecting edges and two original tails, divided by \(Y\), cost at most
\[
 \frac{e^{(u-1)66+w^2(u^2-B^2)/2}}{\pi}
 \left(\frac{(u-s)C}{B}+\frac{\zeta(u)}{\zeta(2u)(wB)^2}\right).
\]
Here \(C\) bounds the reciprocal along the edges using the unsigned [finite-height bandlimited estimate](SHORT_SPECTRUM.md). The tail follows from \(1/t\le t/B^2\) for \(t\ge B\).

The remaining vertical cost is bounded by \(e^{(s-1)x+w^2s^2/2}/\pi\) times the integral on \([0,B]\) of \(e^{-w^2t^2/2}|\zeta(s+it)|^{-1}/\sqrt{s^2+t^2}\). On \([0,100]\) bound the modulus directly on complex balls, split until the supremum of \(|\zeta|\) is no more than twice its positive lower bound, and integrate \(1/\sqrt{s^2+t^2}\) exactly on that cell. Above 100 split at successive factors \(1.3\). Each such cell uses its own archimedean estimates and the Gaussian at the left endpoint. Two methods give valid upper bounds for the reciprocal's integral there.

The first takes the phase-arc supremum in the preceding bandlimited estimate. The second keeps all prime phases as functions of the same \(t\). Its positive multiplier is \(A_0\) from that estimate with the prime sum omitted. Put
\[
 F(t)=\exp\!\left(-\tfrac12\sum_{p^j<e^\kappa}B_{p^j}e^{ijt\log p}\right)
      =\sum_{n\ge1} a_n n^{it}.
\]
Then \(|1/\zeta(s+it)|\le A_0 |F(t)|^2\) on that cell. This series is absolutely convergent, also with any fixed polynomial frequency weight. The finite Euler factorization and Parseval on each unit circle give
\[
 M_\alpha=\sum n^\alpha |a_n|^2
 =\prod_p\frac1\pi\int_0^\pi
 \exp\!\left(-\sum_j B_{p^j}p^{j\alpha/2}\cos(j\theta)\right)d\theta .
\]
The integrals for \(\alpha=0,1\) use 128 full interval enclosures. Also \((\sum |a_n|)^2\le K=\exp(\sum B_{p^j})\).

On any time interval of length \(D\), majorize its indicator by the convolution of two centered indicators of lengths \(D+R,R\), divided by \(R\), translated to its midpoint. Its mass is \(D+R\), and the modulus of its Fourier transform at \(\xi\) is at most \(\min(D+R,4/(R\xi^2))\). If \(m/2\le n\le2m,\ n\ne m\) then \(|\log(n/m)|\ge|m-n|/(2m)\). Use \(2|a_m a_n|\le|a_m|^2+|a_n|^2\) in this symmetric region. For each \(m\), summing the transform bound on either side costs at most \(8m\sqrt{(D+R)/R}\), by integrating the decreasing function \(\min(1,c^2/t^2)\) from zero to infinity. In the remaining region \(|\log(n/m)|\ge\log2\). Altogether
\[
 \int_I|F(t)|^2dt\le(D+R)M_0+16\sqrt{(D+R)/R}\,M_1+\frac{4K}{R(\log2)^2}.
\]
Take the least bound at \(R=D,D/4,D/16,D/64\) and at the four bandlimits \(4,5,6,7\). The physical-length and integration constants are all evaluated with Arb. These are estimates on the sharp signed prefix. Application to Selberg weights requires the separate exact divisor convolution and summation by parts.

~~~sh
python -B round7/mobius/sharp_mertens.py --table
~~~
