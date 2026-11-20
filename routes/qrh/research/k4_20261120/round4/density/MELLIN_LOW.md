# Mellin energy of the filtered low norm

With the notation of [the variance identity](VARIANCE.md), write \(v=1+e,\ 0<e\le e_0=2\delta/U\le .1,\ \eta=\phi(Q)/Q,\ D=2^{\omega(Q)},\ Y_0=e^U h\), with \(\log Y_0>16\). Define \(g(u)=\max(0,\min(1,u/W))\), so \(1-\omega(jn)=g(\log(j/Y)+\log n)\). For \(\mu_Q(n)=\mu(n)\mathbf1_{(n,Q)=1}\) set
\[
 B(u)=\sum_n \mu_Q(n)n^{-1-e}g(u+\log n).
\]
Then \(B(\log(j/Y))=b_{1+e,Q}(j)\) exactly.

## Continuous energy

For \(\Re z>0\), \(\int_{-\infty}^{\infty}e^{-zu}g(u)\,du=(1-e^{-Wz})/(Wz^2)\). Put \(z=e/2+it\). The Fourier transform of \(e^{-eu/2}B(u)\) equals
\[
 \frac{1-e^{-Wz}}{Wz^2}\sum_n\frac{\mu_Q(n)}{n^{1+e-z}}
 =\frac{1-e^{-Wz}}{Wz^2\zeta_Q(1+\bar z)}.
\]
The transforms sum absolutely in \(L^1\) and \(L^2\), since the norm of each translated, weighted function includes only the additional factor \(n^{e/2}\), and \(\sum n^{-1-e/2}\) converges. Fourier–Plancherel and real symmetry therefore give
\[
 I_e=\int_{\mathbb R} e^{-eu}|B(u)|^2\,du
 =\frac1\pi\int_0^\infty
 \frac{|1-e^{-Wz}|^2}{W^2|z|^4|\zeta_Q(1+z)|^2}\,dt.               \tag{1}
\]
The analytic identity is used only at \(e>0\). The scalar majorants used for the first parameter cell extend to \(e=0\).

## Discrete sampling

Let \(J=Y^{2/5}\). On \(j>J\), use a discrepancy bound \(D\) for counts of units in \((J,x]\). For \(x\ge J\) set \(F(x)=Y^e x^{-1-e}|B(\log(x/Y))|^2\). Partial summation gives
\[
 Y^e\sum_{j>J,(j,Q)=1}j^{-1-e}|B(\log(j/Y))|^2
 \le \eta I_e+D\int_J^\infty |F'(x)|\,dx .
\]
The finite-height boundary term vanishes at infinity and the counting discrepancy is zero at the starting point. The weighted integral from \(J\) to infinity is at most its full value \(I_e\).

Uniformly in \(u\), \(|B(u)|\le B_0=1+2/\eta\). Indeed, \(\sum_{n\le x}\mu(n)\lfloor x/n\rfloor=1\) bounds \(|\sum_{n\le x}\mu(n)/n|\le(1+\lfloor x\rfloor)/x\le2\) for \(x\ge1\). Partial summation with \(n^{-e}\) preserves the bound. Convolving with \(Q\)-smooth \(1/k^{1+e}\) costs at most \(1/\eta\). The defining transition represents \(B\) as an average of the complementary sums, whose full Dirichlet series is \(1/\zeta_Q(1+e)\le1\). Moreover \(B\) is Lipschitz with \(|B'(u)|\le B_1=1+1/W\) almost everywhere. The contributing integers in \(W B'(u)\) lie in an interval of ratio \(e^W\), whose harmonic sum is at most \(1+W\). Thus
\[
 D\int_J^\infty |F'|\le D(B_0^2+2B_0B_1)Y^{e-(2/5)(1+e)}.
\]
The upper bound at \(e_0,Y_0\) is valid when the resulting exponent is negative, as checked by the code.

For \(j\le J\) write \(s=\log(Y/j)\) and \(S=(3/5)\log Y_0>\log15\). The two residuals in \(W B(-s)=R_v(s)-R_v(W+s)\) are precisely the errors of the sieved logarithmic Möbius sum relative to its two main terms \(tD_v-F_v\). With \(\xi=1-1/(12\log10)\), \(Z_a=\prod_{p\mid Q}(1-p^{-a})^{-1}\), the uniform bound
\[
 |R_v(s)|\le e^{-es}\{A/s+(C+H_1s)e^{-s/2}\}
\]
holds with \(A=.0336 g_1 2^{e_0}Z_\xi,\ C=(4.86g_0+2.93+5.17e_0)2^{e_0}Z_{1/2}\) and \(H_1=2.83e_0 2^{e_0}Z_{1/2}\). The \(g\)'s are \(1\) when \(Q\) is odd and \(g_0=\sqrt3(\sqrt2-1)/2,\ g_1=1.4378(1-2^{-\xi})\) when \(Q\) is even. Dropping the indicator from the \(A/s\) term keeps an upper bound. [Ramaré–Zuniga Alterman, *Möbius function and primes: an identity factory with applications*, Theorem 1.3](https://arxiv.org/html/2312.05138v2#S1).

Putting \(c=e^{-W/2},\ C'=C(1+c)+H_1Wc,\ H'=H_1(1+c)\) gives
\[
 W|B(-s)|\le e^{-es}\{2A/s+(C'+H's)e^{-s/2}\}.
\]
After squaring, the normalized discrete sum has measure at most \(1/j\) on the bracket. For the first term the sum \(\sum_{j\le J}1/(j s^2)\) is at most \(1/(\log Y_0)^2+1/S\), by monotonicity for \(s>2\) and integral comparison. For the second term the squared norm is \(Y^{-1}\sum_{j\le J}(C'+H'\log(Y/j))^2\), at most its integral on \([0,J]\) since the summand decreases. This is bounded by
\[
 e^{-S}\{(C'+H'S)^2+2H'(C'+H'S)+2(H')^2\}.
\]
The expression is a positive tail integral decreasing with the lower cutoff. Minkowski now gives the quantity called \(\texttt{head}\) in the script.

## Scalar verification of (1)

Split \(e\in[0,e_0]\) into closed cells \([l,u]\). For \(t\le100\), compute the modulus lower bounds for each \(1-p^{-(1+z)}\) and for \(\zeta(1+z)\) on a complex Arb rectangle. For \(t\le1/4\) evaluate \(Z(z)=z\zeta(1+z)\). With \(N=16\), Euler–Maclaurin gives
\[
 \left|Z(z)-N^{-z}-z\sum_{n<N}n^{-1-z}-\tfrac12 zN^{-1-z}\right|
 \le \frac{|z(1+z)|}{12N^2}\left(1+\frac{|2+z|}{2}\right).
\]
In fact the omitted Bernoulli term contributes at most \(|z(1+z)|/(12N^2)\), and the integral remainder is bounded using \(\sup_{[0,1]}|B_2|=1/6\) and \(\int_N^\infty x^{-3-\Re z}\,dx\le1/(2N^2)\). On this part of the integral, \(|(1-e^{-Wz})/(Wz)|\le1\) by its integral representation. Away from zero the script also uses the interval exponential divided by the lower bound on \(W|z|\).

For \(t\ge100\), \(|1/\zeta(1+z)|\le4.339\log t\), and the modulus of the finite Euler product is at least \(\eta\). By (1) the tail cost before division by \(\pi\) is at most
\[
 \frac{4(4.339)^2}{W^2\eta^2 R^3}
 \left\{\frac{\log^2 R}{3}+\frac{2\log R}{9}+\frac2{27}\right\},\qquad R=100 .
\]
The cited strip includes all \(\Re(1+z)\ge1\). [Leong, *Explicit estimates for the logarithmic derivative and the reciprocal of the Riemann zeta-function*, Corollary 4 and Table 5](https://arxiv.org/html/2405.04869v3#S5).

The normalized quantity \(S_Q(1+e)/(Y^{-e}\log T)\) is now at most the sum of the discrete head, the discrepancy error, and \(\eta I_e\), multiplied by
\[
 \frac{1+u\{1/2+(1+u)/12\}}{2\delta}\prod_{p\mid Q}(1-p^{-1-u}).
\]
This bounds \(\zeta_Q(1+e)/\log T\) by the [pole estimate](../../round2/spectrum/POLE_BOUND.md). For \(U=49,\delta=.9,W=10.7,\log h=-4.85,Q=210\), the four cell bounds returned by \(\texttt{mellin_low_rows}\) are smaller than \(.045641,.044194,.042691,.041159\), respectively. A direct norm already includes the entire energy of this sieved coefficient, so it is a separate candidate from the bound obtained by subtracting [the variance](VARIANCE.md) from the unsieved majorant.
