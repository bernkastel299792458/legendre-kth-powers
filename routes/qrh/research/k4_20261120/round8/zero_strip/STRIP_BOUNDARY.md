# Global signed prime phases from both boundaries of the zero strip

Assume QRH(7/8). Put \(H=3000175332800,\ T=He^{7/4},\ s=.865,\ \Theta=7/8,\ b=\Theta-1/2\). Any closed interval of width \(375000000\) inside \([H,T]\) contains at most **419290** zeros with real part at least \(s\), counting multiplicity. For width \(10^9\) the cap is **658675**. For width \(116000000\) it is **256862**. Thus the [second true rectangle](../../round6/reduction/OBSTRUCTION.md) can fail only if the exceptional ordinates span more than **375,000,000**. Both the prior individual doubled population of \(840142\) and the threefold population of \(1260213\) are excluded on their original span of \(10^9\).

There is a separate signed constraint on the **entire height range**. For any nonempty submultiset of \(R\) exceptional zeros let \(S_p=\sum_\rho e^{i\gamma\log p}\). Then at least one prime \(p\le e^{26}\) satisfies \(\Re S_p<-.07612R\), and at least six distinct such primes have \(\Re S_p<-.05R\). There are also at least 156 distinct \(p\le e^{45}\) with \(\Re S_p<-.01R\), and at least 395 distinct \(p\le e^{50}\) with \(\Re S_p<-.005R\).

The frequency and the population are independent of a candidate integer for a fourth-power gap. These are restrictions on actual zeta zeros. The [progression corollary](PROGRESSIONS.md) uses them to exclude several classes of populations that satisfy the previous scalar count inequalities. No bound of \(420070\) for the total count has been obtained.

## Harmonic continuation across the strip

Set \(w(u)=(1-u/A)_+\) on \(u\ge0\), with \(20\le A\le60\), and use the entire function
\[
 h_t(z)=\int_0^A\frac{w(u)}{\cosh(bu)}\cos((z-t)u)\,du .
\]
At both boundaries \(\Im z=\pm b\), its real part is the Fejér kernel \(A\operatorname{sinc}^2(A(\Re z-t)/2)/2\). Its real part is harmonic in the closed strip and tends uniformly to zero at either infinite end, by integration by parts in \(u\). The minimum principle therefore gives \(\Re h_t(z)\ge0\) throughout the strip. This exact boundary continuation differs from the [single half-plane kernel](../../round7/qrh_strip/RIGHT_EDGE.md), which placed a further broadened kernel on the second boundary. Positivity now holds directly for each actual root under QRH.

Apply the unconditional [Guinand–Weil formula, Proposition 5](https://doi.org/10.1007/s00209-021-02820-9) after even symmetrization. The gamma mass is again \(\pi\), as \(w(0)=1\). For the real-line integrand, two integrations by parts give \(|h_t(t+y)|\le(4/A+\pi b/2)/y^2\le1/y^2\): the two endpoint derivatives cost at most \(2/A\), and the second derivative has integral at most \(2/A+b^2\int_0^\infty\operatorname{sech}(bu)du\). At the two pole arguments the real part uses \(w(u)\operatorname{sech}(bu)\cosh(u/2)\) as its coefficient. The sum of its two endpoint derivatives and its integrated absolute second derivative is at most \((2+A)e^{A/2}\), by differentiating the factors and using \(b=3/8,\ A\ge20\). Consequently the same digamma estimate as in the single-kernel proof, with \(|y|=H/10000\) as the cutoff, costs less than .0001 after division of the formula by two, uniformly on \(H-1\le t\le T+1\). The margin includes replacing \(T+1\) by \(T\) inside the logarithm.

Define the finite positive weights
\[
 v_{p,k}=\frac{(\log p)p^{-k\Theta}}{1+p^{-2kb}}(1-k\log p/A)_+ ,
 \qquad P_A(t)=\sum_{p^k\le e^A}v_{p,k}\cos(kt\log p).
\]
The arithmetic term in the formula after division by two is exactly \(-P_A(t)\). Write \(B=\frac14\log(T/(2\pi))+.0001\). For one exceptional zero and its reflected partner at ordinate \(\gamma\), their combined contribution on the same normalization is
\[
 G(y)=\int_0^A w(u)\frac{\cosh((\beta-1/2)u)}{\cosh(bu)}\cos(yu)\,du,\qquad y=t-\gamma.
\]
It is nonnegative for all \(y\). The ratio of hyperbolic cosines lies between \(\exp[-(\Theta-s)u]\) and 1. For \(0< |y|\le2/A\) we can use
\[
 G(y)-B\ge q_A(y):=
 K_A(.01,y)-B-\frac{(A-\pi/(2|y|))_+^2}{2A}
       (1-e^{-.01A})(A|y|-\pi/2)_+ .
\]
Here \(K_A(e,y)=\Re[1/z+(e^{-Az}-1)/(Az^2)]\), \(z=e+iy\). At \(y=0\) omit the last term. The deficit occurs only for \(u>\pi/(2|y|)\); there \(-\cos(yu)\le(A|y|-\pi/2)_+\). The remaining \(w\) integral is the displayed squared positive part divided by \(2A\). This lower profile decreases with \(|y|\) in the stated range.

For all the chosen zero pairs, \(-P_A(t)\ge\sum_\rho G(t-\gamma)-B\). Therefore for any interval \(I\) containing \(R_I\) chosen ordinates, and any additional nonnegative cost \(D+P\),
\[
 \int_{I+[-2/A,2/A]}[-P_A(t)-B_0]_+^2\,dt
 \ge 2R_I\int_0^{2/A}[q_A(y)-B_0]_+^2dy,\qquad B_0=D+P.
\]
This follows by applying \((\sum u_i-B-B_0)_+^2\ge\sum(u_i-B-B_0)_+^2\) for \(u_i\ge0\). Apply the [signed cubic moment calculation](../../round7/qrh_strip/INCREMENT.md) to the new prime coefficients and this lower profile. The code reuses the original exact arithmetic subroutine with its coefficient function replaced in a private namespace. Its upper bound for large-prime coefficient squares remains valid: here the square is bounded by \((1-u/A)^2p^{-2\Theta}\), smaller than that earlier majorant. The old crude tail on \(p>X,\ k\ge2\) also remains valid. All the other cubic, frequency-spacing and interval-endpoint inequalities are unchanged.

| Width | \(A,X,D,b_{\rm cubic}\) | Unrounded upper count |
|---:|---|---:|
| \(10^9\) | \(47,250000,4,.27\) | \(658675.378526\) |
| \(116000000\) | \(42,65000,3.2,.48\) | \(256862.423247\) |
| \(375000000\) | \(44,130000,3.86,.30\) | \(419290.996373\) |

## Moments of the actual phases

At a chosen ordinate, the reflected pair alone gives \(-P_A(\gamma)\ge K_A(.01,0)-B\). Bound powers \(p^k,\ k\ge2\), in absolute value. Write \(v_p=v_{p,1},\ V=\sum_{p\le e^A}v_p\). Summing the inequality at all selected zeros gives
\[
 -R^{-1}\sum_{p\le e^A}v_p\Re S_p\ge D_A,\qquad
 D_A=K_A(.01,0)-B-\sum_{p^k\le e^A,\ k\ge2}v_{p,k}.                  \tag{1}
\]
For the first powers the verifier computes the prefix to \(X=160000\), then bounds the rest by partial summation with \(\vartheta(v)<1.01624v\) and exact \(\vartheta(X)\). The positive decreasing majorant for the tail integrand against \(d\vartheta\) is \(v^{-\Theta}(1-\log v/A)\). For higher powers of \(p>X\) it uses the integral of \((\log t)t^{-2\Theta}/(1-X^{-\Theta})\) over \([X,\infty)\). The input on primes is [Rosser–Schoenfeld, Theorem 9](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf).

| \(A\) | Upper \(V\) | Lower \(D_A\) | Lower \(D_A/V\) |
|---:|---:|---:|---:|
| 26 | 51.34705 | 3.90892 | .07612 |
| 40 | 228.91189 | 9.49184 | .04146 |
| 45 | 388.49871 | 11.37358 | .02927 |
| 50 | 661.70207 | 13.19784 | .01994 |

For a threshold \(c>0\), if just \(k\) primes have \(-\Re S_p>cR\), equation (1) implies that the sum of their weights is at least \((D_A-cV)/(1-c)\). The calculation orders the finite prefix by weight and verifies the comparisons in interval arithmetic afterwards. Every tail weight is at most \(X^{-\Theta}\log X\). This yields the stated counts of distinct frequencies.

One can remove the diagonal and the nearby pairs. At \(A=26\), if \(R\ge420071\), then
\[
 \sum_{\substack{\rho,\rho'\\|\gamma-\gamma'|>450}}
   \sum_{p\le e^{26}}\frac{v_p}{V}\cos((\gamma-\gamma')\log p)
       > .00044080\,R^2 .                                             \tag{2}
\]
Indeed \(\sum(v_p/V)|S_p|^2\ge(D_A/V)^2R^2\) by Cauchy. Fix any central ordinate. Each exceptional zero within 450 brings both members of its reflected pair into a Poisson integral on the 2-line over the enlarged interval of half-width \(450+21\). A point at distance at most 450 contributes at least the integral of the two kernels over \([-21,21]\) around its ordinate. Their parameters add to 3, so concavity of \(\arctan\) on the positive half-line bounds the combined integral below by \(4\arctan(21/1.5)\). The integral of the gamma main term is at most \(2(450+21)[\frac12\log((T+942)/(2\pi))+10^{-9}]\), from the same digamma bound. The integral of the arithmetic part \(\Re\zeta'/\zeta(2+it)\) costs at most \(2\log\zeta(2)\) by termwise integration. Thus each row contains at most 2249.315 near points, including itself and all multiplicities. Charging them by their maximal normalized weight one and subtracting gives (2). This is a lower bound on a signed nonlocal correlation forced by a failing count, not an upper estimate on that correlation.

~~~sh
python -B round8/zero_strip/strip_boundary.py
~~~
