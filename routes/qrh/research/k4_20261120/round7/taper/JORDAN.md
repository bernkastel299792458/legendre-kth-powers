# A positive variance term for the right-side detector norm

## Conditional variance in the second prime coordinate

Let \(p<q\le47\) be the two smallest primes of the radical. In the product-geometric representation below, first condition on all exponents other than the \(p\)-exponent. The expectation of this conditional variance pays for the existing least-prime estimates. The *variance of the conditional mean* remains. Condition that mean on all remaining exponents except that of \(q\); keep the pair of \(q\)-exponents zero and one. Write \(j\) for the radical times the powers at the remaining primes, so that \(v_p(j)=v_q(j)=1\), and \(t=\log(X/j)\). Put \(f_q(t)=G_e(t)-G_e(t-\log q)-G_e(t-W)+G_e(t-W-\log q)\), with \(G_e=0\) at negative arguments. The resulting additional term of the normalized Jordan form is bounded below by summing
\[
 \frac{Y^e j^{-1-e}}{W^2}(1-p^{-1-e})(1-q^{-1-e})q^{-1-e}
 \left|\sum_{m\ge0}p^{-m(1+e)}f_q(t-m\log p)\right|^2 .
\]
The geometric mass at \(p\) enters twice inside the squared conditional expectation and once reciprocally from the radical normalization. The sum over \(m\) is finite because its shifted argument eventually becomes negative. Each radical has a unique ordered pair of smallest primes. This term and the earlier expected conditional variance are different nonnegative terms in the same exact identity.

The required \(j=pqn\) have density \(\frac1{pq}\frac{480}{2310}\prod_{13\le\ell\le q}(1-1/\ell)\), with primes \(\ell\) in the product. If \(q\) is at zero-based index \(i\) among the primes from 13, inclusion–exclusion gives discrepancy at most \(2^{6+i}\). Use \(0\le t\le16\), cells of width \(1/32\), and the signed prefix enclosures described below. The Lipschitz constant of the entire geometric sum on a cell ending at \(b\) is at most \(2(1+b)/(1-p^{-1-e_{\min}})\). The extra deductions on \(\log Y\ge30\) at \(W=8.5,9,9.5,10\) exceed .0000994098, .0000858115, .0000743424, .0000646460 respectively.

~~~powershell
python -B round7/taper/second_jordan.py
~~~

Use \(Q=2310,\ v=1+e,\ .04\le e\le .10,\ Y\ge e^{30},\ X=Y e^W\). The [centered Jordan identity](../../round2/right/PROOF.md) and its [restriction to the units modulo \(Q\)](../../round4/density/VARIANCE.md) give an exact representation of \(S_Q(v)/\zeta_Q(v)\). In its squarefree radical \(r\), set
\[
 b(j)=\sum_{(m,Q)=1}\mu(m)m^{-v}(1-\omega(jm)),\qquad c_r=\prod_{p\mid r}(1-p^{-v}).
\]
The old majorant contribution of this radical is \(r^{-v}\sum_{k\mid r^\infty}k^{-v}b(rk)^2\). The actual contribution is \(r^{-v}c_r|\sum_{k\mid r^\infty}k^{-v}b(rk)|^2\). Their difference is \(r^{-v}c_r^{-1}\operatorname{Var}(b(rK))\) under the product of independent geometric laws giving probability \(c_r k^{-v}\) to \(K=k\).

If \(r\) contains a prime from 13 through 97, condition on the exponents at all primes other than the smallest such \(p\). By total variance the full variance dominates the mean conditional variance in the \(p\)-exponent. Retain the unordered pair of exponents 0 and 1 in that conditional variance. Summing its nonnegative contribution over all these radicals gives at least
\[
 \sum_p (1-p^{-v})p^{-v}
 \sum_{\substack{(j,Q)=1,\ v_p(j)=1\\(\,j,\prod_{13\le q<p}q\,)=1}}
 j^{-v}|b(jp)-b(j)|^2 .
\]
Here products indexed by \(q\) run over primes. The sum over \(j\) follows from the unique decomposition \(j=rk'\) with \(k'\) supported on the other primes of \(r\). No radical or pair is counted twice.

Retain \(Y\le j\le X\) and put \(r_0=\log(X/j)\). Then
\[
 W |b(jp)-b(j)|=
 \left|G_e(r_0)-G_e([r_0-\log p]_+)\right|,
 \quad G_e(t)=\sum_{\substack{m\le e^t\\(m,Q)=1}}\mu(m)m^{-1-e}(t-\log m).
\]
Its undifferenced expression inside the absolute value has Lipschitz constant at most \(1+r_0\) up to \(r_0\); the derivative sums only over the moving window in \(\log m\). Use signed prefixes of \(m^{-1-e}\) and \(m^{-1-e}\log m\) on each closed exponent interval of width .01. In a log cell \([a,b]\) of width \(1/32\), bound the difference at its midpoint and subtract \((1+b)(b-a)/2\). Each \(j\) at a shared endpoint can be assigned to just one cell. The required \(j\)'s form a periodic set of mean \(\eta_p=(\phi(Q)/Q)(1-1/p)p^{-1}\prod_{13\le q<p}(1-1/q)\). After writing \(j=pn\), elementary inclusion–exclusion gives discrepancy at most \(2^{6+i}\) on a half-open interval when \(i\) previous primes from the list have been used. Hence their \(Y^e j^{-1-e}\) mass in this cell is at least
\[
 e^{-e_{\max}(W-a)}
 \left(\eta_p(1-e^{a-b})-2^{6+i}e^{a-W-30}\right)_+ .
\]
The program takes the smallest of the six independently summed lower bounds for \(e\). Subtract the resulting amount from the previously used value \(\eta I_e+\mathrm{discrete\ error}\) before multiplying by the common upper bound for \(\zeta_Q(v)/\log T\). At \(W=8.5,9,9.5,10\) the respective deductions exceed .00065292, .00055731, .00047478, .00040316. These are savings in the normalized arithmetic quadratic form, before applying the other factors in the explicit formula.

~~~sh
python -B round7/taper/jordan_variance.py
~~~

## Smaller integers in the same radical variance

For \(W<r_0=\log(X/j)\le16\), use the disjoint range \(j<Y\). The difference \(W(b(jp)-b(j))\) is, up to a sign, the mixed difference of \(G_e\) with lags \(W,\log p\), extending the function by zero to negative arguments. The same pair of exponents 0 and 1 applies. Its Lipschitz constant on a cell ending at \(b\) is at most \(2(1+b)\), by summing two short harmonic windows. The weight factor here is at least \(\exp(e_{\min}(a-W))\), since \(a\ge W\).

The [inner calculation](inner_jordan.py) uses the [quantized signed prefixes](CAUSAL.md) of \(\mu_Q(n)/n\) and \(\mu_Q(n)\log n/n\). To calculate \(G_e\) on the grid through 16, let \(h=1/256\) and tilt the signed increments on \(a<\log n\le a+h=t\) by the common interval \(e^{-ea}\) for an \(e\)-cell of width .005. With \(N,N'\) the integer endpoints, the discarded variation in the accumulated slope is at most \((N'-N)e^{-e_{\min}a}e_{\max}h/(N+1)\). Its contribution to the new hinge value in that cell is at most \(h\) times this, and an old slope error contributes its size times \(h\). The slope quantization costs at most \((N'-N)2^{-44}\); the new hinge costs at most \((1+t)(N'-N)2^{-44}+160\cdot2^{-52}t(N'-N)/(N+1)\) in the quantized sums. The term at one is kept exact. Interpolate from the lower grid node with Lipschitz constant \(1+t\). Evaluate the mixed differences on physical cells of width \(1/64\), retaining each strictly positive lower bound. For \(W=8.5,9,9.5,10\) this additional normalized deduction exceeds .00022381, .00019010, .00016259, .00013962 respectively.

~~~sh
python -B round7/taper/inner_jordan.py
~~~

For the disjoint radicals with smallest admissible prime \(101\le p\le499\), still use the exponents 0 and 1. With \(j=pn\) require \(n\) to be coprime to every prime from 13 through \(p\), including \(p\) itself. The third-order Bonferroni lower bound gives mean at least \((480/2310)(1-e_1+e_2-e_3)/p\), where \(e_h\) are elementary symmetric sums of the reciprocals of those primes. For each fixed subset the units modulo 2310 have discrepancy at most 32 by inclusion–exclusion, uniformly on half-open intervals after division by the subset product. The total counting error is at most \(32\sum_{h=0}^3\binom{j_p}{h}\), with \(j_p\) the number of primes from 13 through \(p\). Discard any cell with negative count or response lower bound. Use cells of width \(1/32\) through log coordinate 16, with the single or mixed difference on the respective sides of \(W\). The additional deductions at the four widths in the table above exceed .000089365, .000078584, .000069085, .000060608. The inner and rough deductions in this file use \(\log Y\ge30\); at smaller \(Y\) only the outer elementary term at its explicitly certified threshold may be used. Both deductions are replayed by the command above.
