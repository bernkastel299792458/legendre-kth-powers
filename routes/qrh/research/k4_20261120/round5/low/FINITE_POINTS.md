# At the finite-density target, how much does moving the Littlewood line cost?

Let \(N_{>\sigma}(T)\) count positive ordinates through \(T\) with real part strictly greater than \(\sigma\), with multiplicity. The [sufficient finite-density estimate](../spectrum/DENSITY_TARGET.md) uses \(7(\log T) T^{3(1-\sigma)/(3\sigma-1)}\). Evaluate both sides at the same \(T=e^{35}\), without shifting or rounding the requested height. The following rigorously rounded bounds come directly from the distance estimate. For the left endpoint, the modulus-210 and modulus-2310 mollifiers use a short Möbius core of \(2^{17}\); the right endpoint uses the tight Mellin row containing the actual exponent. All analytic assumptions are as in the [round-five moment proof](../spectrum/PROOF.md). These upper bounds on the number of zeros do not prove the sufficient estimate.

| \(\sigma\) | Auxiliary \(s\) | Certified upper bound for \(N_{>\sigma}(e^{35})\) | Target | Upper-bound / target | Universal floor / target in the five cases |
|---:|---:|---:|---:|---:|---:|
| .800 | .7874 | 18,545,209,000 | 800,909,256.26 | 23.16 | >9.07 |
| .825 | .8129 | 2,445,057,800 | 63,015,124.64 | 38.81 | >15.11 |
| .850 | .8393 | 291,380,022 | 6,341,009.45 | 45.96 | >18.11 |
| .860 | .8485 | 121,841,325 | 2,690,010.56 | 45.30 | >17.87 |
| .874 | .8628 | 34,929,333 | 854,143.94 | 40.90 | >16.14 |

The [192-bit verifier](finite_points.py) checks five choices of \((Q,\delta,W,\log h)\), including each winning row. At \(U=\log T=35\) the critical-line bound can take the upper height exponent equal to the lower one in the [short-core calculation](../left/SHORT.md); all one-sided comparisons there include equality. The exponent of the right coefficient is fixed at \(e=2\delta/U\). Thus one can select the last of its 16 closed [frequency and Mellin cells](../spectrum/verify.py) instead of maximizing over all cells down to zero. This yields two integrated boundary upper bounds \(A\) and \(B\). For example the row attaining the displayed .850 upper bound has \(\delta=.85,\ Q=210,\ A=3.08380\ldots\,10^{17},\ B=.270208\ldots\). The registered search over \(s\) chooses only witnesses; it claims no global optimum for those upper bounds.

The [rectangular argument](MOVING_WINDOW.md) gives
\[
 (\sigma-s) N_{>\sigma}(T)
  \leq \sum_{0<\gamma\leq T}(\beta-s)_+
  \leq \frac{c_\nu}{2\pi}\mathcal N^\nu A^{P(s)}B^{1-P(s)}
                +E(s).
\]
Here \(\mathcal N=(1+10^{-6})^2/(1-1/H)\). For this cumulative bound the analytic time window is centered at zero; real coefficients make the two half-axis factors cancel. At each chosen auxiliary abscissa the program reuses the 16-step Jensen radius integral and the sharp right-side divisor tail of the moving-window proof, adding both to the detector with which they were proved. For the additional quintic detector, Taylor expansion at \(|w|<1/4\) gives
\[
 |\log((1+w)(1-w/2)^2(1+w^2/10))|
 \leq |w|^2\left(\frac1{2(1-|w|)}
       +\frac1{4(1-|w|/2)}+\frac{1/10}{1-|w|^2/10}\right)
 <2|w|^2.
\]
Its outer-disk modulus is bounded using degree 5. All Jensen centers are nonzero by the uniform smallness on \(\Re z=2\).

**Lower bound on every radial-detector output using the same two norms.** Let \(\mathcal D\) be any entire function with \(\mathcal D(0)=1,\ \mathcal D(-1)=0\), and suppose \(\log|\mathcal D(w)|\leq c_\nu|w|^\nu\) for all \(w\). By Jensen at radius \(r>1\), \(c_\nu r^\nu\geq\log r\). Taking \(r=\exp(1/\nu)\) gives \(c_\nu\geq1/(e_{\rm nat}\nu)\), where \(e_{\rm nat}=\exp(1)\). This conclusion allows other zeros and any degree.

Drop all positive rectangle and analytic-window losses, retain \(A,B\) as the chosen numerical upper bounds, and write \(x=\sigma-s>0,\ k=\log(A/B),\ a=2-\sigma+3\delta/U,\ c=3(1+2\delta/U)\). The exact interpolation exponents are
\[
 P=3-c/(a+x),\qquad \nu=(2+4\delta/U)/(a+x).
\]
The remaining lower bound on the numerical output for \(N_{>\sigma}\) is
\[
 F(x)=\frac{B\exp(kP)}{2\pi e_{\rm nat}\nu x}.
\]
Its logarithmic derivative has the sign of \((ck-a)x-a^2\). Since \(ck>a\), the global minimum occurs exactly at \(x=a^2/(ck-a)\), including the possibility of relaxing the original domain of \(s\) to all \(x>0\) in this scalar expression. This analytic minimum is what the last table column bounds from below, taking the least over all five tested norm choices. It is a lower bound on the best output of this proof method with those fixed numerical norms. It places no lower bound on the actual zero count. In a fixed-height relaxation, a collection of independent hinge bounds all gives constraints \(N\leq M_s/(\sigma-s)\) on a pile of mass arbitrarily close to \(\sigma\) from the right. Their infimum already contains the strength of all such constraints at this abscissa.

The same script also supplies a positive part of the continuous target. For every \(H\leq T\leq H+5\,000\,000\) and **all 75** abscissae \(.800,.801,\ldots,.874\), the desired bound with coefficient 7 holds. This uses the [frozen short-window fourth moment](FROZEN_FOURTH.md). At each abscissa its direct cumulative bound at the upper endpoint is compared with the target at \(H\). Monotonicity covers every intervening real height. The largest ratio is below \(0.964696\), attained at .874. For example the upper bounds at .800, .850 and .874 are respectively \(4,238,113,\ 469,029,\ 156,879\). The grant of this short region does not by itself establish the first discrete target, which has a substantially higher ordinate.

Applications at other fixed abscissae can import \(\texttt{fixed}(U,\delta,W,\log h,Q,\texttt{core})\), followed by \(\texttt{counts}(\sigma,U,\delta,*\texttt{fixed}(\cdots))\). The output contains the certified upper bound, its auxiliary abscissa, and the radial-detector floor for that fixed pair of norms.
At the .850 witness, \(P=.44988361\ldots\). Keeping this witness and detector fixed, an improvement obtained exclusively in \(A\) would have to exceed \(45.951^{1/P}>4953\); one obtained exclusively in \(B\) would have to exceed \(45.951^{1/(1-P)}>1051\). The additive rectangle terms are positive and only increase these requirements. Simultaneous improvements of both norms enter as \(A^P B^{1-P}\).
For the six alternate abscissae \(\sigma=.800,.813,.826,.839,.852,.865\), the coefficient can be lowered from 7 to 6 throughout \(H\leq T\leq H+6\,500\,000\). The same script directly verifies all six bounds with a worst ratio below \(0.998523\). This proves an initial continuous part of the stronger six-node criterion; its first proposed discrete height lies beyond the certified window.

At the intermediate ordinate itself, the direct moving-window argument bounds \(N_{>.85}(e^{35}+10^8)-N_{>.85}(e^{35})\) by \(6,164,859\). The same calculation gives \(2,458,913\) at .865 and \(1,436,045\) at .874. Here the existing global fourth-moment estimate already suffices; the center moves to \(e^{35}+5\cdot10^7\). The left geometric height remains \(>200\), and all holomorphic window and denominator estimates remain valid at the larger ordinate. The frozen parameters and upper-endpoint limiting argument are as before; approach the lower endpoint from above so its zeros are excluded. No claim of verification of RH through \(e^{35}\) is needed. These are bounds on the increments in that window. They do not give cumulative bounds through \(e^{35}\).

With the integer Gram calculation at the higher location the width can be enlarged tenfold: \(N_{>.85}(e^{35}+10^9)-N_{>.85}(e^{35})\leq5,178,953\). This calculation used the coarse harmonic norm and exact coprimality sieve at 2, 3, 5 and 7 on the unweighted norm; at the larger cutoff the code skips the full harmonic array. It gives \(2,060,913\) and \(1,190,107\) at .865 and .874. Replay this separate high-height computation with:

~~~sh
python -B round5/low/finite_points.py --billion
~~~
