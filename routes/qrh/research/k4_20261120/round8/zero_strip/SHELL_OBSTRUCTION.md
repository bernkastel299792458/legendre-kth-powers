# A full-height obstruction for independent prime blocks

Assume the [strip detector](STRIP_BOUNDARY.md) with \(20\le A\le60\), the second rectangle \(\beta\ge s=.865,\ H\le\gamma\le T\), and the desired count \(M=420070\). Allow an arbitrary partition of the first-prime terms into sets, arbitrary nonnegative thresholds for those sets, and arbitrary moment degrees and nonnegative shifts. Grant zero cost to the omitted small primes and every higher prime power. Combine the square-root costs of the positive parts by the triangle inequality, and use the full single-zero profile on the whole real line.

For this calculation, even using exact Euler diagonal means on each remaining set and allowing an independent exponential Chernoff parameter on each set, the resulting full-height expression cannot reach \(M\), throughout \(20\le A\le60\). This conclusion applies to the two integrals in (2) below. It allows the usual Hilbert error proportional to the frequency integer on the whole polynomial. A mean estimate with cancellation among the frequency errors, a detector retaining correlations between separate blocks, or different zero information is outside this obstruction.

The exact-diagonal certificate discards all primes \(p\le e^8\) throughout the continuous bandwidth range. A common certificate also rules out every positive mixture of those bandwidths, with the same free primes and at least a **1.7498%** excess over the mixture's available peak budget. When \(A=40\) one may discard every \(p\le e^{10}\); the budget still needed is at least **10.67888205**, whereas at most **10.45945782** is available. Of this witness, the intervals \(10<\log p\le15\) and \(20<\log p\le25\) contribute 3.49996 and 3.24652, respectively. With the common factorial diagonal estimate, even discarding all primes \(p\le e^{18}\) leaves a required **10.49156987**. These are lower bounds on proof costs, not lower bounds on the area of actual exceptional values or on the number of zeros.

## The single-zero budget

Write \(W=T-H,\ B=\frac14\log(T/(2\pi))+.0001\). A uniform proof by this method must allow zeros at real part \(s\), with profile \(G_A\) from the strip detector. Its ratio of hyperbolic cosines exceeds \(e^{-.01u}\) by at most \(.02u e^{-.74u}\); integration gives an error below .04 at every ordinate. The product of this ratio with the triangular weight decreases from one to zero, so integration by parts gives \(G_A(y)\le1/|y|\). Thus \((G_A-B)_+\) is supported on \(|y|\le1/B\).

In a bandwidth cell \(A_0\le A\le A_1\), put \(Q=K_{A_1}(.01,0)+.04-B\). For all \(D\ge0\),
\[
 \|[G_A-B-D]_+\|_2\le (Q-D)_+
   \left\|[G_A-B]_+/Q\right\|_2 .
\]
Calculate an upper bound \(\kappa\) for \(\sqrt{M/W}\) times the last norm. The verifier uses 512 equal cells on \([0,1/B]\), with reflection. In each, \(G_A\) is at most \(K_{A_0}(.01,y_{\rm mid})+.04+(A_1-A_0)/2 + A_0^2\Delta y/12\), since the integral of the increase in the triangular weight is \((A_1-A_0)/2\), and the first absolute derivative moment is at most \(A_0^2/6\). Consequently, if block \(J\) uses threshold \(D_J\ge0\) and supplies a normalized square-root upper cost \(L_J\) for its positive part, success requires
\[
 \sum_J(D_J+L_J/\kappa)\le Q.                                         \tag{1}
\]
The normalized mean here divides the underlying square integral by \(W\); actual endpoint extensions and extra terms can only cost more in the tested upper bound.

## The two Hilbert integrals

Write \(a_p=v_{p,1},\ \epsilon=4.2/W\). Let the \(Z_p\) be independent uniform unit phases. The integrals used by the moment bound have their ordinary diagonal and the additional length-weighted diagonal
\[
 \mu(F)=\mathbb E\,F\!\left(\sum_{p\in J}a_pZ_p\right)
    +\epsilon\,\mathbb E\,F\!\left(\sum_{p\in J}\sqrt p\,a_pZ_p\right). \tag{2}
\]
For \(F(z)=|b-z|^{2d}\) this is precisely the complex Dirichlet-polynomial diagonal pair with its frequency weight \(n\). We even allow the smaller real powers \(F(z)=(b-\Re z)^{2d}\) on these same two tori. For \(d\ge2\), the pointwise polynomial majorant of the positive part charges
\[
  L_J=\frac{(d-1)^{d-1}}{d^d}
       \frac{\mu(F)^{1/2}}{(D_J+b)^{d-1}},\qquad b\ge0 .
\]
Minimizing \(D_J+L_J/\kappa\) over \(D_J+b>0\) gives the lower bound \(\kappa^{-1/d}\mu(F)^{1/(2d)}-b\). For \(d=1\) allow the unshifted real bound \(\sqrt{(B_0+\epsilon B_1)/2}\), with \(B_j=\sum_{p\in J}p^j a_p^2\), or its unhelpful shifted version. Direct uniform payment \(\sum_{p\in J}a_p\) is allowed too.

The exponential option uses \((x-D)_+\le e^{\lambda(x-D)-1}/\lambda,\ \lambda>0\). In (2) the corresponding mean is exactly \(\prod I_0(2\lambda a_p)+\epsilon\prod I_0(2\lambda\sqrt p\,a_p)\). This also covers applying the positive-part exponential estimate through an analytic Dirichlet exponential and evaluating its two squares as Euler products.

## A dual certificate for every exact degree

Construct numbers \(g_p\ge0\), each at most \(a_p\), and write \(G_J=\sum_{p\in J}g_p\). The first-degree constraint is \(\sum_p g_p^2/[a_p^2(1+\epsilon p)]\le1/(2\kappa^2)\). Cauchy gives \(D_J+L_J/\kappa\ge G_J\) for all sets \(J\).

For the real fourth moment, \(\mathbb E(\Re Z)^4=3/8\) for a uniform unit phase \(Z\). Expanding with distinct independent phases yields \(\mathbb E(b-\Re\sum a_pZ_p)^4\ge (b^2+c B_0)^2,\ c=\sqrt{3/8}\), and the weighted integral obeys the same bound with \(B_1\). Indeed the fourth term is \(3B_0^2/4-3\sum a_p^4/8\), and the quadratic term is \(3b^2 B_0\). Put \(t=1/\sqrt2,\ e=\sqrt\epsilon\). Euclidean duality and minimization over \(b\) give
\[
 \kappa^{-1/2}\mu(F)^{1/4}-b
 \ge \left[c t\big(\kappa^{-1}-1/[t(1+e)]\big)(B_0+e B_1)\right]^{1/2}.
\]
The corresponding weighted ellipsoid constraint again ensures \(G_J\) is no larger than the last expression.

For every higher moment use a single probability measure \(\nu_J\) on the two branches of (2). Give its ordinary Haar branch mass \(1-w\), and its weighted branch mass \(w\). On the weighted branch take independent phase densities \(1-2u_p\cos\theta_p\), where \(u_p=g_p/(w\sqrt p\,a_p)\). Then \(\mathbb E_{\nu_J}[-\Re z]=G_J\). The verifier enforces \(0\le u_p<.03\) and \(\sum_{p\in J}u_p^2\le S=2.5\), uniformly over all subsets.

With \(q=6/5\), Taylor's formula and \(\mathbb E\cos^2\theta=1/2\) give \(\mathbb E(1-2u\cos\theta)^q\le\exp(q(q-1)u^2/(1-.06))\). Choose \(w\) so that
\[
 \int (d\nu_J/d\mu)^q d\mu
 \le (1-w)^q+\epsilon^{1-q}w^q\exp(q(q-1)S/(1-.06))
 <\kappa^{-2(q-1)} .
\]
Log convexity of the power integrals and \(\int d\nu_J=1\) extend this bound to every \(1<q'\le6/5\), replacing \(q\) on its right by \(q'\). Hölder with \(q'=2d/(2d-1)\) proves \(\kappa^{-1/d}\mu(F)^{1/(2d)}\ge b+G_J\) for all \(d\ge3\). Taking the derivative at \(q'=1\) yields \(\int\log(d\nu_J/d\mu)d\nu_J\le\log(\kappa^{-2})\). Jensen now gives \(\mu(e^{-2\lambda\Re z})\ge\kappa^2 e^{2\lambda G_J}\). The exponential payment satisfies \(D_J+L_J/\kappa\ge G_J\) by \(e^{u-1}\ge u\). This uses the actual torus moments, retaining every multiplicative collision.

## The factorial version

For the usual complex upper expression, the \(j\)th ordinary factorial diagonal is
\(\sum_{k=0}^d {d\choose k}^2 k! b^{2(d-k)} B_j^k\ge(b^2+c_d B_j)^d,\ c_d=(d!)^{1/d}\), since the geometric mean of the first \(k\) descending factors of \(d!\) is at least the full geometric mean. For \(d\ge2\), put \(e_d=\epsilon^{1/d},\ t_d=2^{-1+1/d}\). Duality of the two-coordinate \(d\)-norm gives the same squared-cost surrogate as for the fourth moment, with
\[
  h_d=c_d t_d\!\left[\kappa^{-2/d}-\frac1{t_d(1+e_d)}\right],
  \qquad G_J^2\le h_d(B_0+e_d B_1).
\]
All \(d\le32\) are checked directly. For \(d\ge33\), \(t_d\ge1/2,\ 1/[t_d(1+e_d)]\le\epsilon^{-1/(2d)}\). Since \(c_d\ge d/e\), one can use the uniform factors \(h_d\ge(-2\log\kappa+\tfrac12\log\epsilon)/(2e)\) and \(e_d\ge\epsilon^{1/33}\).

## Interval computation and the arbitrary partition

Use bins of log width \(1/32\). In one such bin \((l,r]\) the first-prime weight at \(A_0\) lies between \(a_-=l e^{-\Theta r}(1-r/A_0)/(1+e^{-.75l})\) and \(a_+=r e^{-\Theta l}(1-l/A_0)\). Its squared mass is at least \(C_i=n_i a_-^2\), where \(n_i\) is a certified lower bound on the number of primes. The finite sieve gives exact counts through \(e^{16}\). Above that point use \(\#\ge[\vartheta(e^r)-\vartheta(e^l)]/r\) and \(|\vartheta(x)-x|\le .2x/\log^2x\) for \(x>3594641\). [Dusart, Theorem 5.2](https://arxiv.org/pdf/1002.0442)

Choose rational candidate masses \(g_i\) numerically, then certify the required normalized ellipsoid inequalities and the pointwise cap \(g_i\le C_i/a_+\) in Arb. To see that whole-bin constraints imply arbitrary partitions, distribute \(g_i\) among primes in proportion to their actual \(a_p(A_0)^2\). This gives total squared normalized mass at most \(g_i^2/C_i\), and maximum \(g_p/a_p(A_0)\le g_i a_+/C_i\). Monotonicity in \(A\) extends these inequalities to every bandwidth in the cell. Deleting any set of primes from an ellipsoid only decreases its sum. Thus the same witness works on both sides of every cut, including cuts through the verification bins. The certificate checks \(\sum_i g_i>Q\), contradicting (1) for the stated method. The minimum certified excess for the exact model over the 50 closed bandwidth cells is **.02648766**.

## One witness for a positive mixture of all bandwidths

Let \(\nu\) be any probability measure on \([20,60]\) and use the mixture of the original strip profiles and their prime coefficients. With \(Q_A=K_A(.01,0)+.04-B,\ Q_\nu=\int Q_A\,d\nu(A)\), pointwise convexity followed by Minkowski gives
\[
 \left\|\frac{[\int G_A\,d\nu(A)-B]_+}{Q_\nu}\right\|_2
 \le \int\frac{Q_A}{Q_\nu}\left\|\frac{[G_A-B]_+}{Q_A}\right\|_2 d\nu(A).
\]
The same inequality with the common additional threshold as in (1) applies to this profile. The new verifier uses 640 cells of width \(1/16\) and the previous ordinate subdivision. In each bandwidth cell the numerator uses the upper majorant from above, and the denominator uses \(Q_{A_0}\). This gives the single \(\kappa=.000055\) for every mixture; the largest certified actual ratio times \(\sqrt{M/W}\) is below .000054745.

To construct a common tilt, choose **exactly** \(n_i\) arbitrary primes in each log bin, using the integer floor of the certified lower count there, and disregard bins with zero count. Assign to each of them the dimensionless number \(v_p=z_i/\sqrt{n_i}\). Its contribution for a bandwidth \(A\) is \(g_p(A)=v_p a_p(A)\). All first- and fourth-moment ellipsoid constraints now involve just the \(v_p\)'s and the frequencies \(p\), independently of the chosen prime coefficients. The higher-moment and exponential constraints have the same property, with \(u_p=v_p/(w\sqrt p)\), \(w=.124\). For the mixed coefficients one takes \(g_p(\nu)=v_p\int a_p(A)d\nu(A)\). A zero coefficient has zero charge and can be omitted.

The proposed nonnegative \(z_i\)'s are rounded to rational input and checked on the three ellipsoids, the individual caps and the Rényi bound. For \(i\)th log bin \((l_i,r_i]\), put \(M_i=z_i\sqrt{n_i}\,l_i e^{-.875r_i}/(1+e^{-.75l_i})\). The contribution to \(\sum_p g_p(A)\) is at least \(M_i(1-r_i/A)_+\). Each bandwidth cell compares the sum of these lower bounds at its left endpoint against \(Q_A\) at the right endpoint. Every resulting ratio is at least **1.0174986874**. Integrating in \(A\) gives this same lower factor times \(Q_\nu\) for the true mixed coefficients, which contradicts (1) for this method. This applies to adding the active detectors with arbitrary fixed positive weights. A nonlinear estimate of simultaneous exceedance using different zero inputs is a distinct method.

## A genuinely notched positive boundary test

Take the normalized autocorrelation of the indicator of \([0,15]\cup[40,55]\). Its even Fourier weight on the positive half-line is \(w(u)=(1-u/15)_++\tfrac12(1-|u-40|/15)_+\). Its transform on the strip boundary is nonnegative as a squared modulus. Harmonic continuation again divides \(w(u)\) by \(\cosh(3u/8)\). This removes the entire open frequency band \(15<u<25\), including one of the costly intervals identified above.

Here the primes on the opposite flank, \(40<\log p\le54\), already rule out using (1) and (2). Even granting the improved archimedean budget \(B=7\), the maximal peak is less than 5.215485. This follows by integrating \(w(u)e^{-.01u}\) explicitly and adding the same .04 as above. Writing \(r(u)=\cosh((s-1/2)u)/\cosh(3u/8)\), the total variation of \(wr\) on the positive axis is at most \(1+3/2\). The initial triangle times \(r\) decreases from 1. The satellite uses the product variation inequality with height \(1/2\), variation 1 and \(\operatorname{Var}(r)\le1\). Therefore \(|G(y)|\le2.5/|y|\) and \(\kappa=.000146\) is a common upper allowance for this profile.

Let \(\mathcal E=\sum_{40<\log p\le54}p a_p^2\). The unconditional prime-count bounds above give \(\mathcal E>4217960.6781\). Put \(c_0=\sqrt{\epsilon/(2\kappa^2)}\) and take \(g_p=c_0 p a_p^2/\sqrt{\mathcal E}\) on this interval, zero elsewhere. The first ellipsoid holds since \(1+\epsilon p\ge\epsilon p\). The fourth holds because \(c_0^2<h_2\sqrt\epsilon\), using the exact real fourth coefficient above. With branch mass .05 the high-degree tilt has \(\sum u_p^2=(c_0/.05)^2\), and the pointwise and Rényi bounds are verified directly. Indeed \(g_p/a_p\le c_0\cdot54e^{.125\cdot54}/\sqrt{\mathcal E}<1\), and \(u_p\le (g_p/a_p)e^{-20}/.05<.03\). This subset therefore costs more than **5.3973132** by itself. This test addresses the specified pair of intervals.

~~~sh
python -B round8/zero_strip/shell_obstruction.py
python -B round8/zero_strip/mixed_shells.py
python -B round8/zero_strip/notch.py
~~~
