# Lower range from sieving the actual exterior intervals

For \(x=n^4\), every positive integer \(n\le3115778011799\) has a prime in \((n^4,(n+1)^4)\) using the published finite-height RH verification and the finite results on this route. Under QRH(7/8) this reaches \(n=3120455185821\). The new local part proves the stronger statement for every real \(x\) in the indicated closed log-slabs, with a prime in \((x,x+4x^{3/4})\). The unconditional continuation starts at the [squarefree Farey endpoint](../../round5/low/SQUAREFREE_FAREY.md). The proof uses the [location-sensitive Selberg bound](BILINEAR.md) only where both length and location lie inside its certified ranges.

| Hypothesis above the verified zero height | Closed \(\log x\) slab | Complete normalized error below |
|---|---|---:|
| Unrestricted zeros | \([115.034625,115.0695]\) | 0.999873447185 |
| Unrestricted zeros | \([115.0695,115.0700]\) | 0.999976994227 |
| QRH(7/8) | \([115.0700,115.0760]\) | 0.999976568221 |

Use the kernel and all prime-power, far-tail, pole, gamma-factor and verified-zero terms of the [signed edge proof](../../round2/local/EDGE.md) with the [physical positive-lobe refinement](../../round5/low/PHYSICAL_TAIL.md). The new sieve saving concerns only the two first exterior lobes and the next 64 reflected pairs, entirely inside \(|\log p-c|\le r=10^{-6}\). Other exterior lobes continue to use the global addition \(1.16613\); their full infinite tail remains included. Write \(l\le\log x\le h,\ c=\log x+\tfrac12\log(1+4x^{-1/4})\), and put \(c_+=h+\tfrac12\log(1+4e^{-l/4})\). For an angular superlevel width \(w\in[w_-,w_+]\) the corresponding actual interval in the prime variable has length between
\[
       e^{l-r}w_-/K\quad\text{and}\quad e^{c_++r}w_+/K .
\]
Its endpoints are bounded by \(e^{l-r}\) and \(e^{c_++r}\). The script checks these strictly within \([e^{114.98},e^{115.12}]\). A local saving is available only when both length bounds lie between \(e^{83}\) and \(e^{89}\). Take the smallest Selberg denominator among all the certified log-length cells that could meet the enclosure. The global sieve remains available without any local savings on the other levels.

For scale \(s>0\), write \(C_1(\eta,s),C_2(\eta,s)\) for the slope and intercept in the cited edge proof. Concavity of \(2y/(\log y+\eta)\) on the applicable interval permits the same tangent even if its point of tangency is outside that particular log-length cell. The sieve itself is only asserted at the actual length. Both coefficients decrease with \(c\) by the inequalities checked in the script; normalization and endpoint Jacobians are the earlier ones.

On the first lobe the source uses 8192 superlevel cells, each with positive height difference \(\Delta\), \(w_0\le w\le w_1\), and \(s=(w_0+w_1)/2\). Replacing its tangent at the old addition by one at \(\eta\) saves at least
\[
 2\Delta\max\left(0,C_{2,\rm old}-C_{2,\rm new}
  +\min_{w=w_0,w_1}(C_{1,\rm old}-C_{1,\rm new})w\right)
\]
for the pair. The old proof had first charged a common slope to the exact total area; subtracting this pointwise guaranteed gain also lowers its upper integrated correction.

On the secondary lobes use exactly the source's 256 angular cells and 128 bands of levels through the value at the lobe midpoint. A lower bound on the physical superlevel width counts all angular cells with lower values above the band; an upper bound counts all cells whose upper bound could exceed its bottom. The true superlevel is an interval by log concavity. The old source subtracted from its reference line a fixed gain per level, the maximum over three tested scales and zero. Recompute that old gain with the same angular grid and scales. Compute the new gain against the **same reference** from the local sieve, and charge only the positive difference of the new and old gains. This replaces each old bound by the smaller of two sound bounds and does not reuse the same saving twice. The levels above the midpoint and all secondary lobes after the 64th retain their former upper charges.

For the two unconditional slabs \(K=H-206000,\ H=3000175332800\); use the original Gaussian tail for every unverified ordinate. For the QRH slab use \(K=H+16000000000\) and the upper bound \(0.005937108818\) for the finite high-zero charge certified in [the 96-window reference](../first_selected/LOW_CONTINUATION.md) on \([115.040500,115.041000]\). Both endpoints of the present slab have increased, so the arithmetic-independent spectral charge transfers with factor one. Indeed the new \(a\le a_0\), both are between \(\pi/2\) and \(\pi\), and \(\sin a\ge\sin a_0\). At each ordinate the truncated-sine numerator of the old cap increases with \(a\), and its denominator is \(\sin a\); hence the new whole cap is at most the old. The positive-ordinate weights \(e^{(\beta-1)l}\) decrease as well. The negligible remote Gaussian beyond \(K+128\cdot10000\) is evaluated at the new \(a\). This argument bounds pointwise caps and does not require monotonicity of their differences. The integer endpoints come from the Arb floors of \(e^{115.0700/4}\) and \(e^{115.0760/4}\). The old and new slabs meet at their closed endpoints.

Run from the directory containing the round folders. The QRH line additionally uses the finite high-zero reference command in the file linked above.

~~~powershell
python -B round7/physical/bilinear.py
python -B round7/physical/cover.py --lo 115.034625 --hi 115.0695 --eta auto --check
python -B round7/physical/cover.py --lo 115.0695 --hi 115.0700 --eta auto --check
python -B round7/physical/cover.py --lo 115.0700 --hi 115.0760 --eta auto --size 16000000000 --high .005937108818 --check
~~~

The elementary special-purpose sieve has no QRH dependence. The full infinite fourth-powers statement still needs the intervening ranges of the prime-interval argument.
