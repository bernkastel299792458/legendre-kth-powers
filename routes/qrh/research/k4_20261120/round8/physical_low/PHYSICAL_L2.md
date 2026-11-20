# All Mellin frequencies of the actual physical Möbius product at \(L=116\)

Use \(X_-,X,z,F,P_0,u,I,A,S_0,c,r,H,Y\) and \(\delta=.0002 e^{116}/H\) from [the signed-band condition](REMAINING_PHASE.md), with \(P_0=u H e^{-c}\). Each entry bounds the absolute value **after** summing the signed coefficients over every true modulus, with the exact integer multiplier \(k\). No restriction on \((k,q)\) is imposed. This is cancellation between different actual moduli.

| Wheel \(Q\) | \(k\) | Outer spectral energy | Low twisted energy | Discrete transport | Common-prime cost | Entire signed physical upper |
|---:|---:|---:|---:|---:|---:|---:|
|210|11|.002440811161|.000000896842|.000006357755|.000133089808|.002581155563|
|210|23|.001753111289|.000001651723|.000004566454|.000095590825|.001854920289|
|223092870|97|.000563948624|.000014973594|.000001468958|.000008196624|.000588587798|
|223092870|131|.000468375857|.000011992597|.000001220012|.000006834609|.000488423074|

For \(Q=23\#,\ m=200\) the complete prefix \(q>X/m\), all low phases, \(q\le e^{70.7}\), and the previously specified high tail are paid, leaving a signed allowance above .00176077404. For \(m=239\) it remains above .00014108785. The earlier positive-integer calculation reached \(m=131\) with allowance .00030954645. The proof of the remaining signed band is still open.

## Factorization before any absolute value

At fixed \(k\) write \(d=g j,e=g l\). Then the exact common divisor is \(g\), the modulus is \(q=g j l\), and \(n=kg j l\). Expand the Selberg numerators over the two auxiliary squarefree indices \(b,t\) as in [the presieved physical proof](PRESIEVED_PREFIX.md). In each ordered \(g,b,t\) cell the coefficient is
\[
 \frac{\rho(g)^2}{G_Q(z)^2\varphi(b)\varphi(t)}\,
 \mu(j)\rho(j)\mu(l)\rho(l).
\]
Here \(g,b,t\) are squarefree with \((g,Q)=(bt,gQ)=1\), \(gbt<k\). The two rows are units modulo \(Qgb,Qgt\) respectively and \((j,l)=1\). The support of \(F\) permits restricting the first row to \(a_1<j\le b_1\) and the second to \(a_2<l\le b_2\), where
\[
 a_1=X_-t/(kz),\ b_1=z/(gb),\qquad
 a_2=X_-b/(kz),\ b_2=z/(gt),\qquad
 \ell=\log(b_1/a_1)=\log(b_2/a_2).
\]
Nonpositive spans contribute zero. Exchange both rows to arrange \(b\ge t\) and use multiplicity two for \(b>t\). First omit \((j,l)=1\), then pay the common-prime correction below.

## Removing lattice atoms on a much finer scale than the prime interval

Put \(f(v)=e^{v/H} F(e^{c+v/H})\), and denote a signed row by the atomic measure
\[
 d\nu_i=\sum_{\substack{a_i<n\le b_i\\(n,Q_i)=1}}
   \frac{\mu(n)\rho(n)}n\,\delta_{\log n}.
\]
The raw physical product is \(e^c/(kg)\) times the integral of \(f(H(\log(kg)+y_1+y_2-c))\) against \(d\nu_1d\nu_2\). Convolve each measure independently with the uniform probability on \([-\epsilon,\epsilon]\), \(\epsilon=.0003/H\). Both the signed density and the similarly convolved absolute measure are pointwise bounded in modulus by
\[
 V_i=Z_Q\bigl(\eta+E/(2\epsilon a_i)\bigr),\quad
 \eta=\varphi(Q)/Q,\quad E=2^{\omega(Q)}(1+\log z),\quad
 Z_Q=\prod_{p\nmid Q}(1+1/(p(p-1))).
\]
Indeed the ordinary \(\rho(n)\)-count over a unit interval \((l,h]\subset(0,z]\) is at most \(Z_Q(\eta(h-l)+E)\) by positive divisor expansion and the ordinary unit discrepancy. Partial summation gives the reciprocal count \(Z_Q(\eta\log(h/l)+E/l)\). Intersect the averaging interval with the actual row, so its log length is at most \(2\epsilon\) and \(l\ge a_i\). The smoothed row has support of length at most \(\ell+2\epsilon\). Write \(\mathcal E=(\ell+2\epsilon)V_1V_2\).

The total variation of \(f\) is at most \(V_f=2e^{2r}S_0+M/H\), where \(M=e^{2r}A+2(.0002)e^{116-c}S_0\) bounds \(\int f\). The original physical weight has total variation at most twice its summed peak heights, and dilation of its superlevel intervals cannot increase their number. Convolution with a probability cannot increase the total variation. The variation of the factor \(e^{v/H}\) adds at most \(M/H\).

In the transport comparison, on each realization of the two independent shifts compare the original and displaced value of \(f\). Its absolute difference is at most the variation measure of \(f\) on the interval centered at the **displaced** ordinate with radius \(2H\epsilon\). The integral of this majorant on the real ordinate line is \(4H\epsilon V_f\). Integrate it against the two independently displaced absolute measures. Bounding their densities by \(V_i\), integrating one ordinate on the whole line and the other over its support, gives the cost \(4\epsilon V_f\mathcal E\) before the physical prefactor. This justifies smoothing both indices irrespective of the original sign and its very short interval.

## Exact Fourier shape and the unbounded tail

Use \(\widehat f(s)=\int f(v)e^{-isv}dv\). For \(f_\infty(v)=g_a(v){\bf1}_{\cos v<\cos a}\), \(g_a(v)=(\cos a-\cos v)/(v^2-a^2)\), put \(h_0=1-a/\pi,\ h_j=-\sin(ja)/(\pi j)\) for nonzero integer \(j\). The spectrum of \(g_a\) is \((\pi/a)\sin(a(1-|s|)){\bf1}_{|s|\le1}\), as follows by integrating its inverse cosine transform twice (or by elementary product-to-sum). The \(h_j\) are the Fourier coefficients of the periodic indicator. Apply its Fejér means first and use dominated convergence with \(g_a\in L^1\). For \(j\ge0,\ 0\le v\le1\) the exact result is
\[
 \widehat f_\infty(j+v)=\frac{\pi}a
 [ h_j\sin(a(1-v))+h_{j+1}\sin(av)] .
\]
The negative axis is even. With \(U=Hr\) the error from the actual physical weight is uniformly at most
\[
 E_f=2(.0002)e^{116-c}S_0+(e^r-1)A+
      {4\over U(1-(a/U)^2)} .
\]
The first term integrates \(F-W\ge0\) in the original physical variable, the second changes its logarithmic Jacobian, and the last integrates the discarded tails of \(g_a\). Since \(0<a<\pi/2\), the expression on \([0,1]\) decreases. For \(1\le |s|\le2\), use \(I(|h_1|+|h_2|)\). For \(|s|\ge2\) use \(5I/(6\pi)\). Thus, on \(|s|\ge\tau=.4\), a uniform upper \(B_\tau<M\) for \(|\widehat f(s)|\) is the largest of these latter two bounds and \(|\widehat f_\infty(\tau)|\), plus \(E_f\).

The low Fourier region \(|w|\le\tau H\) uses the [verified finite annulus estimate for the true Möbius/totient coefficients](../../round7/mobius/TWISTED_RMS.md), on the single closed band \(0\le w\le\tau H\). This gives the root-mean-square \(R_i\) for \(\widehat\nu_i(w)\) with \(\sigma=.58,\ u_*=1.55,\kappa_0=6\), and smoothing width \(e^{-22}\) in that arithmetic lemma. These parameters are independent of the much finer spatial boxes above. Bound the row endpoints uniformly by rounding \(\log a_i\) down and \(\log b_i\le\log z\) up. Multiply its analytic portion by \(\prod_{p\mid Q_i,\,p\nmid210}(1-\rho(p)p^{-.58})^{-1}\), as in [the coprime band proof](COPAIR_BAND.md). The positive unsmoothing remainder needs no added factor since the omitted primes only remove terms. Real coefficients allow reflection of the band. Box averaging multiplies the original Fourier row by a sinc of modulus at most one.

By Plancherel and Cauchy, the \(dw/(2\pi)\)-integral of the absolute product of the two smoothed Fourier rows is at most \(\mathcal E\). On \(|w|\le\tau H\) it is at most \(\tau H R_1R_2/\pi\). The spatial convolution introduces the scaling \(H^{-1}\widehat f(w/H)\); the shift \(\log(kg)-c\) has unit modulus. Thus the sum of the spectral and transport bounds in this cell, after applying \(P_0\), is at most
\[
 {\mathcal P} \left[
 B_\tau\mathcal E+(M-B_\tau)\frac{\tau H}{\pi}R_1R_2+
                  4H\epsilon V_f\mathcal E\right],\qquad
 \mathcal P=\frac{u\,\rho(g)^2}{kg\,G_Q(z)^2\varphi(b)\varphi(t)}.
\]
This directly covers every Mellin ordinate. No estimates for \(1/\zeta\) beyond the verified height are used.

## Common-prime correction

Every spurious pair has \(j=pj'\), \(l=pl'\), \(p\nmid Q\). Bound its absolute value by summing over all such common primes, so tuples with multiple common primes may be counted more than once. The upper \(\rho(pj')\rho(pl')\le \rho(p)^2\rho(j')\rho(l')\) and the unit restrictions on both \(j',l'\) are enough. Apply the positive \(\rho\)-weighted count to \(l'\) on each component of every translated superlevel of \(F(kgp^2 j'l')\). The continuous length is divided by \(kgp^2j'\). For the first row \(a_1/p<j'\le b_1/p\), its harmonic upper is \(Z_Q(\eta\ell+Ep/a_1)\); for its unweighted upper use simply \(Z_Q b_1/p\), from positive divisor expansion with the floor bound. These terms give the further cell cost
\[
 \mathcal P Z_Q^2\left[
 M\eta\bigl(\eta\ell\,C_2+EC_1/a_1\bigr)+kgH e^{-c} S_0 E b_1 C_1\right],
\]
where \(C_2\ge\sum_{p\nmid Q}(p-1)^{-2}\), and \(C_1=(11/10)^2(1+\log z)\ge\sum_{p\le z,p\nmid Q}\rho(p)^2/p\). The physical normalization \(H e^{-c}\) on the superlevel intercept is retained. Sum the four cell costs. The accounting for \(q\le Y\), the inverse mean, low-phase and high-phase terms remains as in [the large-wheel proof](WHEEL_PREFIX.md).

~~~powershell
python -B round8/physical_low/physical_l2.py --Q 223092870 --k 97 --upper .000588587798
python -B round8/physical_low/physical_l2.py --Q 210 --k 11 --upper .002581155563
python -B round8/physical_low/wheel_prefix.py --Q 223092870 --cut 200 --harmonic-limit 223092870 --tiny-log 70.7 --unit-small --fast-low --physical-spectrum --lower .00176077404
python -B round8/physical_low/wheel_prefix.py --Q 223092870 --cut 239 --harmonic-limit 223092870 --tiny-log 70.7 --unit-small --fast-low --physical-spectrum --lower .00014108785
~~~

2026-11-20. Joint project attribution to Claude and Codex.
