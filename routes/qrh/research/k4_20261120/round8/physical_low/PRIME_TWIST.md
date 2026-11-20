# Genuine prime-row twists on the identified finite-height band

Put \(I=[H/8,H/4]\), \(H=3000175332800\). Uniformly for \(A\le B\le2A\) at \(\log A=55\),
\[
 \sup_{t\in I}\left|\sum_{A<p\le B}p^{-1-it}\right|<2.241\,10^{-10},
 \qquad\int_I\left|\sum_{A<p\le B}p^{-1-it}\right|^2dt<1.883\,10^{-8}.
\]
The corresponding unnormalized integrals are below \(2.989\,10^{-7}\) and .003186 at \(\log A=52,43\). The only nontrivial zero-location input is RH for \(|\gamma|\le H_0=3\cdot10^{12}\). [Platt and Trudgian, *The Riemann hypothesis is true up to \(3\cdot10^{12}\)*](https://arxiv.org/abs/2004.09765)

Let \(w=1.1\,10^{-11}\). Convolve the indicator of \((\log A,\log y]\) in the log variable with the centered Gaussian of standard deviation \(w\), for each \(A\le y\le2A\). Its bilateral Mellin multiplier is
\[
 W(s)=e^{w^2s^2/2}(y^s-A^s)/s.
\]
The smoothed sum of \(\Lambda(n)n^{-1-it}\) equals \(W(-it)-\sum_\rho W(\rho-1-it)\) plus the vertical line remainder on \(\Re v=-1\) of \(-(\zeta'/\zeta)(v)W(v-1-it)\), with factor \(1/(2\pi i)\). Start on \(\Re v=2\) by absolute convergence of the Dirichlet series and Gaussian inversion. The Gaussian justifies shifting to \(-1\): the symmetric partial fraction expansion allows horizontal heights tending to infinity a distance \(\gg1/\log T\) from every zero there, on which the logarithmic derivative is \(O(\log^2 T)\) in the fixed strip. For completeness, the unit zero count below gives such heights by deleting small intervals around the ordinates. Subtract the value of the partial fraction at \(2+iT\); the near ordinates contribute \(O(\log^2T)\), and the rest \(O(\log T)\) by summing \(O((1+|T-\gamma|)^{-2})\) with that count. The functional equation bounds any remaining gamma factors polynomially. No trivial zero is crossed, and the residue at the pole costs at most \(2/t\).

The number of signed ordinates in any interval \([v-1/2,v+1/2]\) is at most \(12+2\log(|v|+3)\). Indeed the true completed-zeta partial fraction at \(s=2+iv\) gives
\[
 \sum_\rho\Re\frac1{s-\rho}
 =\Re\left(\frac1s+\frac1{s-1}-\frac{\log\pi}2
      +\tfrac12\psi(s/2)+\frac{\zeta'}{\zeta}(s)\right)
 \le5+\tfrac12\log(|v|+3).
\]
Here \(|\zeta'/\zeta(2+iv)|\le-\zeta'(2)/\zeta(2)<1\); the last inequality follows, for example, by bounding the defining sums or direct Arb enclosure. The digamma series for \(\psi(1+ih)\) is bounded using \(\sum_{n\ge1}\min(1/n,|h|/n^2)\le2+\log(2+|h|)\). Each counted zero contributes at least \(8/17\). The additive real constant in the symmetric partial fraction vanishes by the functional equation and the symmetry of the zeros about the critical line.

Put \(C=12+2\log(H+5)\). For finite-height zeros apply their actual real part \(1/2\), group in unit cells on either side of \(t\), and use
\[
 |W(\rho-1-it)|\le e^{w^2/8}A^{-1/2}
                       \min(\log 2,2/|\gamma-t|).
\]
The total is at most \(2Ce^{w^2/8} A^{-1/2}[\log2+2(1+\log(2H+2))]\). Outside the verified range use only \(0\le\beta\le1\). Group \(j\le|\gamma-t|<j+1\), \(j\ge j_0=H_0-H/4-2\). Each of the two unit counts is at most \(C+2j/H\). Splitting the Gaussian exponent in half and dropping \(1/|\gamma-t|\le1\), the sum there is bounded by
\[
 4e^{w^2/2-(w j_0)^2/4}
 \big[C(1+\sqrt\pi/w)+(2/H)(2+4/w^2)\big].
\]
The estimates on the two Gaussian sums follow by comparing the nonnegative unimodal summands with their integrals plus their maxima. On the new vertical line \(|\zeta'/\zeta(-1+iv)|\le10+\log(3+|v|)\) by the functional equation, \(|\cot(\pi(-1+iv)/2)|\le1\) and the same digamma series at \(2-iv\). Integrate \(2A^{-2}e^{2w^2}e^{-w^2(v-t)^2/2}\) against that bound and divide by \(2\pi\); use \(\log(3+|v|)\le\log(3+H)+|v-t|/(3+H)\).

To remove the Gaussian at an endpoint \(b=A\) or \(y\), the difference is bounded by the normal tail at \(|\log(n/b)|/w\). On \([b/2,2b]\), \(\log n/n\le2\log(4A)/A\), or more sharply \(2\log(4A)/b\). The sum of the normal tail over all integers is at most \(2+b e^{w^2/2}\operatorname{erf}(w/\sqrt2)\), by unimodality and the real integral. Off that local interval use \(\log n/n\le1\), extracting \(\exp(-(\log2)^2/(4w^2))\), and bound the remaining Gaussian sum by \(2+2b\sqrt\pi\,w e^{w^2}\). These estimates are uniform for every upper endpoint \(y\). Prime powers of exponent at least two have total weight at most \(\log(2A)[\sqrt{2A}+(2A)^{1/3}\log(2A)/\log2]/A\). Finally partial summation removes the factor \(\log p\), dividing the uniform prefix bound by \(\log A\). This proves the displayed estimates.

## Actual ordinary Mellin contribution

For contrast with the frequency ratio \(\kappa=nX/(Qq)\) in the [physical Fourier condition](REMAINING_PHASE.md), the following is an ordinary Mellin integral of the full physical count. For \(Q=210\), write \(\zeta_Q(s)=\zeta(s)\prod_{p\mid Q}(1-p^{-s})\). On \(I\), \(|\zeta_Q(1+it)|<7.492708\). Indeed, if \(D\) is the maximum elementary discrepancy \(|\#\{k\le v:(k,Q)=1\}-\eta v|\) over one period, \(\eta=\varphi(Q)/Q\), then truncation at \(N=\lceil DH/(4\eta)\rceil+O(1)\) costs at most \(\eta/|t|+D(1+|1+it|)/N\). The first \(N\) terms in absolute value are at most \(\eta(\log N+\gamma+\sum_{p\mid Q}\log p/(p-1))+16/N\) by divisor inversion of harmonic sums. The program uses a specific upward-rounded integer \(N\).

Put \(D_0=\lfloor z/11\rfloor\) and select the [balanced semiprime family](PHASE_FLOOR.md), \(q=pr,\ D_0<p,r\le2D_0,\ p\ne r\). For these moduli the two contributions are positive and \(|\lambda_p|=\rho(p)/G_Q(z)\). In the Mellin strip \(\Re s=1\) the polynomial is the prime row squared, excluding its prime-square diagonal. The piece of the inversion integral on \(I\) and \(-I\) has magnitude at most
\[
 \frac{P_0(\int F)\sup_I|\zeta_Q(1+it)|}{\pi G_Q(z)^2}
 \left[\rho(D_0)^2\int_I\sup_{D_0\le b\le2D_0}
 \left|\sum_{D_0<p\le b}p^{-1-it}\right|^2dt
       + |I|\rho(D_0)^2/D_0\right]<8.615\,10^{-9}.
\]
Here \(\rho(D_0)\) in the last display means the upper bound \(D_0/(D_0-1)\) for the *prime* ratio, and the diagonal bound follows from \(\sum_{n>D_0} n^{-2}\le1/D_0\). Multiplying a prime row by the positive decreasing factor \(p/(p-1)\) costs at most this same upper bound by partial summation. The prefactor is below .740522. This is a bound on the indicated genuine Mellin piece; it is not a bound on the fixed physical angular interval by itself.

~~~powershell
python -B round8/physical_low/prime_twist.py --loga 55 --upper 1.883e-8 --square
python -B round8/physical_low/row_calibration.py
~~~

## Full hard hyperbolic annuli on the true Mellin band

Take every semiprime \(X/m<q=pr\le X/23\), with no restriction on the two prime-size ratios. The whole ordinary Mellin contribution of \(I\) and \(-I\) has absolute value below **.000171679** at \(m=400\) and **.000602916** at \(m=1100\). These are genuine Mellin subintegrals of the physical expression. The [all-frequency resummation](SEMIPRIME_ANNULI.md) is a separate bound.

Set \(P=X/(mz)\). The actual primes satisfy \(P<p,r\le z\), with \(P>m,\ G_{Qp}(z/p)=G_Q(z/p)\). Fix \(w_1=5.5\,10^{-11}\) and mollify the interval \((\log(X/m),\log(X/23)]\) in \(\log q\) by the centered Gaussian of standard deviation \(w_1\). Its Fourier transform, including the inverse \(1/(2\pi)\), has \(L^1\)-norm at most
\[
 [\log(m/23)+2(\log(1/w_1)+1)]/\pi;
\]
the mass outside \(|v|\le H/16\) is at most \((2/\pi)e^{-(w_1H/16)^2/2}/(w_1H/16)^2\). Both follow from the difference of two endpoint exponentials divided by \(iv\). Inside that range \(H/16\le t-v\le5H/16\). The original uniform prime-row estimate applies on this enlarged twist interval. Split \(P<p\le z\) into dyadic intervals and sum their maximal prefix bounds; these totals are \(3.092\,10^{-9}\) and \(5.131\,10^{-9}\) at the two values of \(m\). The positive weight \(\rho(p)G_Q(z/p)\) is decreasing, so one partial summation costs at most \(P G_Q(m)/(P-1)\). The Gaussian Fourier integral now factors into a square of the true prime row. Use the preceding coefficient .740522, the interval length and the Fourier \(L^1\) bound to integrate. The far Fourier tail can use the ordinary prime harmonic upper bound \([\log(z/P)+2E(z)/P]/\log P\), where \(E(z)=\sqrt z\log^2z/(8\pi)\). The prime-square diagonal is bounded directly by \(\sum_{p>P}p^{-2}\le1/(P-1)\).

To restore the hard annulus, each endpoint \(Q_*=X/b\), \(b=23\) or \(m\), contributes a normal tail at \(|\log(q/Q_*)|/w_1\). Outside \(|\log(q/Q_*)|\le r/4\), use \(e^{-(r/w_1)^2/32}\). On each near-endpoint strip, for each fixed prime \(p\), the remaining positive \(1/p'\)-weighted Gaussian tails sum to at most
\[
 e^{r/4}(w_1e^{w_1^2/2}+2/P).
\]
This follows by bounding \(1/p'\) by \(e^{r/4}/(Q_*/p)\), then counting *all* integers by the unimodal integral and its endpoint discrepancy. The outer harmonic bound remains as above. To bound the Mellin integral in this thin strip, for each position \(v\) in the support of \(F\) set \(s=v/q\). The physical dilation implies \(|\log v-c|\le1.01r\), hence \(s/b\) lies between \(e^{-3.26r}\) and \(e^{-.74r}\). Truncate \(\zeta_Q(1+it)\) at \(N\) (the implementation uses the integer \(H^3\)); the integrated remainder on \(I\) is below one by the unit-residue discrepancy. For each integer factor \(k\le N\), the magnitude of the time integral of \(e^{it\log(s/k)}\) is at most \(2/|\log(s/k)|\). The possible resonant integer \(k=b\) costs at most \(4/(23r)\) after including \(1/k\). For \(k\le2m,\ k\ne b\), one has \(|k-s|\ge.9|k-b|\) and \(|\log(s/k)|\ge|k-s|/(2m)\). All remaining \(k>2m\) give \(|\log(s/k)|\ge\log2\). Thus the summed bound is
\[
 4/(23r)+(4m/.9)(1+\log(2m))+2(1+\log N)/\log2+1 .
\]
Multiply by the near-endpoint masses and integrate the positive spatial weight \(F\). This bounds both hard-edge errors together by \(9.124\,10^{-7}\) and \(1.575\,10^{-6}\), respectively. The offset of \(X=e^{c+2r}\) from the actual support is used here.

~~~powershell
python -B round8/physical_low/prime_mellin_annulus.py --end 400 --upper .000171679
python -B round8/physical_low/prime_mellin_annulus.py --end 1100 --upper .000602916
~~~
