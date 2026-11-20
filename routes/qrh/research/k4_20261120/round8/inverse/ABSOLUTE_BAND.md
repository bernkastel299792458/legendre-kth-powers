# A lower bound on the actual absolute Mellin cost in the unknown zero band

Work at \(L=116,\ \log z=38,\ J=6,\ K=H=3000175332800,\ Q=10000\), with the parity weight and its certified ordinary allowance \(0.038766340269\ldots\) from [the target verifier](../physical_low/parity_target.py). Put \(c=L+\frac12\log(1+4e^{-L/4})\) and retain its \(a,I=\pi\sin(a)/a\). Assume QRH(7/8). Consider a Mellin contour deformed from \(\Re s=2\), with the zeta poles of the **integrand** excluded by detours or by cutting out disjoint rectangles. Its sides include the horizontal joins. Assume the region between these sides and the 2-line contains no integrand poles and has finite piecewise-smooth boundary in every bounded height band. Suppose its sides lie in \(m\le\Re s\le2\) for \(H\le|\Im s|\le7H\), where \(m\ge.70\). Then the normalized **absolute** sum over the sides in that band is at least
\[
 26233271590198\ \exp((m-1)c).                                        \tag{1}
\]
For \(m=.70562\) this is already \(>0.03877303024\). Consequently any such absolute-value treatment reaching the desired allowance must go to the left of \(\Re s=.705618513\) somewhere in the two bands. The estimate is for the actual arithmetic product, allowing arbitrary zeta multiplicities. It does not require an estimate on \(1/\zeta'(\rho)\). It places no lower bound on the magnitude of the original **signed** Liouville sum.

There is also a constraint on long excursions: in the positive subband \([1.1H,1.6H]\), take any disjoint height intervals of lengths \(V_i\) throughout which all contour sides have \(\Re s\ge.8751\). If the absolute treatment succeeds, then
\[
 \sum_i (V_i-602)_+ < 33202.
\tag{2}
\]
In particular a single such excursion of height \(33804\) already exceeds the entire allowance. The existing [local zero counts](../../round7/qrh_strip/INCREMENT.md) do not assert any excursion of this length. The condition measures an absolute-cost limitation rather than proving that the needed deformations cannot exist.

## The exact arithmetic product and the frequency normalization

Let \(\ell(n)=(-1)^{\Omega(n)}\), \(S_z(n)=\sum_{d\mid n,d\le z}\lambda_d\) for the original Selberg weights. By complete multiplicativity the Dirichlet series on \(\Re s>1\) is
\[
 F(s)=\sum_{n\ge1}\ell(n)S_z(n)^2 n^{-s}
 =\frac{\zeta(2s)}{\zeta(s)}
 \sum_{d,e\le z}\lambda_d\lambda_e\ell([d,e])[d,e]^{-s}.              \tag{3}
\]
The coefficient \(a_1=1\). For squarefree \(d\), the formula
\(|\lambda_d|=(d/\varphi(d))G_d(z/d)/G(z)\le1\) follows by retaining the terms \(km\) with \(k\mid d,\ m\le z/d,\ (m,d)=1\) in \(G(z)\); \(\sum_{k\mid d}\varphi(k)^{-1}=d/\varphi(d)\). The other \(\lambda_d\) vanish. We use the convenient loose bounds \(|a_n|\le n^4\), and \(|a_n|,|\sum\lambda_d\lambda_e\ell([d,e])[d,e]^{-s}|\le e^{152}\) for \(\Re s\ge0\), where the latter bound on \(a_n\) is uniform in \(n\).

Write \(P(y)=g(y)\sum_{j=0}^6 b_j\cos(jy)\) for the actual degree-six majorant multiplier evaluated by the target verifier. The normalized Mellin differential, omitting its sign and unit phase, has absolute density
\[
 \frac{e^{(\sigma-1)c}}{4\pi I}|F(\sigma+it)|\,|K\mathcal W_\sigma(t)|\,|ds|,
\quad
 \mathcal W_\sigma(t)=\int_{\mathbb R}(c+v)e^{-Q^2v^2+(\sigma-1/2+it)v}P(Kv)\,dv.
\tag{4}
\]
Indeed Mellin inversion of the weight for \(n^{-1/2}\log n\) contributes the factor \(e^{(\sigma-1/2)c}\), and the stated normalization divides by \(2e^{c/2}I/K\).

Use the transform with phase \(e^{-iy\xi}\). The transform of \(g\) is \(\pi\sin(a(1-|\xi|))_+/a\) on \([-1,1]\), with zero continuation outside; equivalently, on the support use \(\sin(a(1-|\xi|))\). This follows by convolution of the two phase-shifted unit-width rectangles corresponding to its sinc factors. Thus, for \(1\le j\le6,\ 0\le v\le1,\ b_7=0\),
\[
 \widehat P(j+v)=\frac{\pi}{2a}\{b_j\sin(a(1-v))+b_{j+1}\sin(av)\}.    \tag{5}
\]
The verifier integrates its absolute value analytically. Each sign-changing cell has one crossing, since \(\sin(a(1-v))/\sin(av)\) decreases from infinity to zero. Direct convolution of (5) with the shifted complex Gaussian gives, uniformly on \(.70\le\sigma\le2\),
\[
 |K\mathcal W_\sigma(t)-c\widehat P(t/K)|
 \le \frac{\pi\sum|b_j|}{K}e^{(3/2)^2/(4Q^2)}
 \left[(c+3/(4Q^2))\,2Q/\sqrt\pi+1\right].                        \tag{6}
\]
To see this, set \(d=\sigma-1/2\). In the convolution, at Gaussian displacement \(u\), the multiplier is \(e^{(d+iu)^2/(4Q^2)}[c+(d+iu)/(2Q^2)]/(2\sqrt\pi Q)\), whose integral is \(c\). The real-profile discrepancy is at most \(\pi\sum|b_j|\,|u|/K\). The first two absolute Gaussian moments are \(2Q/\sqrt\pi\) and \(2Q^2\).

## Uniform good heights and the local Cauchy test

Every unit interval in the two bands contains a horizontal line at distance at least \(r=.001\) from all zero ordinates. Indeed the completed-zeta identity gives \(\sum_\rho P_{2-\beta}(t-\gamma)=\Re\xi'/\xi(2+it)<17\) for \(H-2\le|t|\le7H+2\); here \(P_b(y)=b/(b^2+y^2)\). This uses \(|\zeta'/\zeta(2+it)|\le-\zeta'(2)/\zeta(2)\) and the digamma bound in the [right-edge proof](../../round7/qrh_strip/RIGHT_EDGE.md). A zero within distance 2 contributes more than .14. Thus the union of the \(2r\)-wide exclusions for all such ordinates covers less than one unit. One may also avoid the finitely many boundary vertices and the exceptional nontransverse levels of the smooth pieces.

At such a good height, \(|F(v+it)|\le e^{430}\) simultaneously for \(.70\le v\le2\). For each zero, its integrated contribution to \(\log|\xi(2+it)/\xi(v+it)|\) is
\[
 \tfrac12\log[(b^2+y^2)/((v-\beta)^2+y^2)],\qquad b=2-\beta .
\]
This is at most \(16P_b(y)\). Indeed its ratio to \(P_b\) can be bounded by discarding the nonnegative \((v-\beta)^2\) in the denominator. The resulting \((b^2+y^2)\log(1+b^2/y^2)/(2b)\) decreases with \(|y|\). At \(|y|=r\) use \(1.125\le b\le1.875\). After summation the logarithm is at most 272. The remaining completed-zeta factors to recover \(|1/\zeta(v+it)|\) cost less than 30: the quadratic factor ratio is at most one, the pi factor is below 3, and Euler's beta integral gives \(|\Gamma(v/2+iy)/\Gamma(1+iy)|\le\Gamma(v/2)<5\). Use also \(|1/\zeta(2+it)|<2\). Finally \(|\zeta(2v+2it)|\le\zeta(1.4)\). These estimates justify both horizontal cuts without any separation assumption at the other heights.

Take a height cell \([l,r']\) between good levels. If there are excised rectangles, close the cut by the horizontal segments in the remaining region; their total length at each endpoint is at most 1.3 since their interiors are disjoint. For \(t_0\) at distance at least \(30w\) from each endpoint use the entire test \(\exp((s-2-it_0)^2/w^2)\). On the complete 2-line the integral against \(F(s)\), divided by \(i\sqrt\pi w\), is
\[
 \sum_{n\ge1}a_n n^{-2-it_0}\exp(-w^2\log^2 n/4).
\]
For \(w=300\) this differs from 1 by less than \(10^{-100}\): half the Gaussian exponent absorbs \(n^{-6}\) for \(n\ge2\) and the other half costs at most \(e^{-w^2\log^2 2/8}\); the coefficient bound \(n^4\) suffices. The two deleted tails on the 2-line cost at most \(2e^{152}\zeta(2)w e^{-900}\). The two horizontal cuts together cost at most \(2.6 e^{430+1.69/w^2-900}\). Cauchy's theorem therefore bounds the absolute value of the integral on the other boundary pieces in this cell below by \((1-10^{-90})\sqrt\pi w\). Integrate the centers \(t_0\) continuously over \([l+30w,r'-30w]\). For each boundary point the integral of the Gaussian absolute value over the centers is at most \(e^{1.69/w^2}\sqrt\pi w\). It follows that
\[
 \int_{\text{other sides in cell}} |F(s)|\,|ds|
 \ \ge (1-10^{-90})e^{-1.69/w^2}(r'-l-60w).                         \tag{7}
\]
For (2) use \(w=10\), when the Dirichlet-series relative error is below .002 and \(1-10^{-90}\) can be replaced by .997. Choose the two good heights inside the given interval, losing at most 2 in width. In this subband \(-\widehat P>.52\) by (5). Inserting (6) and (7) in (4) gives (2). Thus the length limitation is for the actual product even on a deformed path.

## Integrating the real spectrum

Split each \([jH,(j+1)H]\), \(j=1,\ldots,6\), into \(N=8192\) equal parts, and cut at good heights within 1 of the nominal nodes, with inner endpoint displacements at \(H,7H\). Repeat at negative heights. Within each nominal cell the available profile minimum is at least the cell-average of \(|\widehat P|\) minus \(L_j/(2N)\), with \(L_j=\pi(|b_j|+|b_{j+1}|)/2\). This follows by integrating the distance to a minimizer. The displacements of the good heights cost at most \(\pi\sum|b_j|/H\) more. When summing use the positive part of each lower bound before applying (7), so replacing all the lengths by their common lower bound is legitimate. With \(E_\mathcal W\) the error in (6), the dimensionless profile mass retained on the positive band is at least
\[
 \int_1^7|\widehat P(v)|\,dv-\sum_{j=1}^6 L_j/(2N)
       -6\{\pi\sum|b_j|/H+E_\mathcal W/c\}.
\]
Multiply by \(cH/(2\pi I)\), by \((1-(2+60w)N/H)(1-10^{-90})e^{-1.69/w^2}\), and by \(e^{(m-1)c}\) to obtain (1). The effective positive and negative band mass before the small losses is \((2\pi I)^{-1}\int_1^7|\widehat P(v)|dv=0.07539661278\ldots\).

## An explicit bound away from local zero ordinates

For numerical comparison, fix \(s<u\), \(u>1,\ u+s>2\Theta,\ \beta_0<s\). If \(|t-\gamma|\ge r\) for every zero with \(\beta>\beta_0\), let
\[
 \Lambda_*=\max\left\{(u-\beta_0)\log[(u-\beta_0)/(s-\beta_0)],\
 \sup_{\beta_0\le b\le\Theta}\frac{(u-b)^2+r^2}{2(u-b)}
 \log\frac{(u-b)^2+r^2}{(s-b)^2+r^2}\right\}.
\]
The first expression follows from the integrated Poisson kernel at \(y=0\). It increases with the zero real part up to \(\beta_0\). For the second, the ratio to \(P_{u-b}(y)\) is maximized at \(|y|=r\), by the chord inequality for \(-\log(1-v)\); the restriction on \(u+s\) ensures the integrated kernel is nonnegative. The completed logarithmic derivative, integrated with respect to the abscissa, then gives
\[
 |1/\zeta(s+it)|\le \frac{\zeta(u)}{\zeta(2u)}
 \exp\left\{\tfrac12(\Lambda_*-h)\log(|t|/(2\pi))
      +\Lambda_*[-\zeta'(u)/\zeta(u)]+10^{-9}(\Lambda_*+h)\right\},
 \qquad h=u-s .
\]
The small gamma error holds on \(H\le|t|\le7H\) for the tabulated abscissae. On a join going to the right this same reciprocal majorant can be applied by retaining the integral bound for the larger kernel, with the gamma subtraction adjusted to the actual abscissa. For example \(s=.60,\ u=1.185,\ \beta_0=.50,\ r=.25\) gives \(1.015\cdot10^8\) as an upper bound on the exposed good portions. Integrating this coarse estimate over the full band size already gives 18.786 before including the Selberg polynomial and \(\zeta(2s)\). At \(s=.645,\ u=1.18,\ \beta_0=.55\) the corresponding figure is 764.45. These are upper-bound costs of this particular estimate, not lower bounds on zeta or on the desired twist. The verifier separately includes the pointwise lcm polynomial majorant \(z^{2-2s}\zeta(2-s)/(1-s)^2\), obtained by grouping the pairs by their gcd and using \(|\lambda_d|\le1\). No count input proves the assumed local clearance across the full band.

## Subtracting an ordinary initial Dirichlet polynomial

Subtracting \(a_1\) analytically removes the normalization in (7). More generally set \(F_Y(s)=F(s)-\sum_{n\le Y}a_n n^{-s}\) with the **true signed coefficients** of (3). For \(Y<100000007\) the original physical contribution of the explicitly removed terms is negligible because \(\log n-c<-97\) and \(Q=10000\). Nevertheless, if the contour stays in \(.8751\le\Re s\le2\) throughout the two subbands \(1.1H\le|t|\le1.6H\), its absolute cost **after any such subtraction** is still \(>.06503717\).

Indeed \(p=100000007\) is prime and \(p>Y\). Its remaining coefficient has \(|a_p|=(1+\lambda_p)^2\). The preceding Selberg formula and the [Ramaré estimates for \(G\)](../../round7/physical/BILINEAR.md) give
\[
 |\lambda_p|\le\frac{p}{p-1}\frac{\log(z/p)+2+2.44/\sqrt{z/p}}{39.331}<1,\qquad
 |a_p|>.20370527 .
\]
Use the same test on each of these two bands, now multiplied by \(p^{s-2}\), and use \(w=26p\). On \(\Re s=2\) the term \(n=p\) contributes modulus \(|a_p|/p^2\) in the normalized Gaussian integral. For \(p/2\le n\le2p,\ n\ne p\), one has \(|a_n|\le\tau(n)^2\le4n\) and \(|\log(n/p)|\ge|n-p|/(2p)\). The resulting leakage is bounded by \(16r/[p(1-r)]\) for \(r=\exp[-(w/(4p))^2]\). The remaining \(n\)'s cost at most \(2e^{152}\exp(-w^2\log^2 2/4)\). The new product inside the two connecting cuts is bounded by \(e^{431}\) since \(Y^5<e^{100}\); the Gaussian tails on the 2-line can still use \(2e^{152}\zeta(2)\). The verifier checks that the combined error, divided by \(\sqrt\pi w\) when appropriate, is less than \(|a_p|/(1000p^2)\).

Consequently (7) holds with \(|F_Y(s)|p^{\sigma-2}\) on the left and with the factor \(.999|a_p|/p^2\) on the right, after selecting the two good heights inside each band (total loss at most two per band). Finally \(e^{(\sigma-1)c}p^{2-\sigma}\) increases with \(\sigma\), since \(c>\log p\). Use the minimum at \(.8751\) and the same \(.52c\) profile bound as in (2) to get the stated cost. Longer or non-prefix subtractions and a signed height integral require separate estimates.

~~~sh
python -B round8/inverse/absolute_band.py
~~~
