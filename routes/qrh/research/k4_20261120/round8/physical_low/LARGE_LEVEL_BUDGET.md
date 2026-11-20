# Complete large- and small-modulus diagnostic at L=116

Let \(x=e^{116}\), \(C=3000000\), \(K=H=3000175332800\), \(z=C\sqrt{x/H}\), \(r=10^{-6}\), \(T=C^2/H\). We use the Logan test, normalization and physical centering of [the first-lobe lower bound](SPIKE_FLOOR.md). The ordinary main term, older analytic terms and the region \(r<|v|\le.01\) are bounded above by .996047187418, .000000046472 and .000001708870. The remaining budget is .003951057243.

For each cut the two conributions exhaust the ordered Selberg pairs and have disjoint support on those pairs. These values are diagnostics of the indicated bounds; they do not increase fourth-power coverage.

| \(R\) | Upper charge for actual \(q>x/R\), including signed inverse moment | Full test upper, exact cut | Full test upper, moving entire crossed rectangles to direct side |
|---:|---:|---:|---:|
|1|.052333|263033481|17001086|
|2|.138799|335310726|14246700|
|4|.339999|334642187|11699365|
|8|.737088|292227357|9606950|

In the exact-cut run at \(R=1\), grouping by \(s=g_{\rm lo}2^{i+j}\) places \(2.46032\,10^8\) of the bound in \(s<T\), i.e. exactly the crossed blocks in this run; \(g\le2\) is singleton there. Grouping the same charge by frequency instead places \(1.60553\,10^8\) in \(2^{32}\le n<2^{40}\). Moving the crossed rectangles to direct evaluation reduces the total to \(1.70011\,10^7\), with the biggest frequency bucket still \(2^{32}\le n<2^{40}\), contributing \(9.04593\,10^6\). The biggest remaining geometric bucket is \(T\le s<4T\), contributing \(5.30172\,10^6\). At \(R=8\) the complete-rectangle version instead peaks at \(2^{24}\le n<2^{32}\), contributing \(4.72588\,10^6\), and \(16T\le s<64T\), contributing \(3.19135\,10^6\). The earlier ordinary short-interval sieve supplies much smaller overall upper bounds; these figures isolate the losses of applying the large-level Fourier estimates per group.

## Direct evaluation

Write \(g=(d,e),\ D=z/(g2^i),F=z/(g2^j),\ d=gu,e=gv\). Then \(D/2<u\le D,F/2<v\le F\), \((u,v)=1\), and \(q=guv\). With \(X_\pm=e^{c\pm2r}\), the possible multiple \(kq\) requires \(k\le4X_+/(gDF)\); for \(q>x/R\) also \(k\le X_+R/x\). For such a \(k\), \(u\) lies between \(A=\max(D/2,\max(X_-,kx/R)/(gkF))\) and \(B=\min(D,2X_+/(gkF))\). These are generous bounds for the near lobes restricted by radius \(r\). The one-point coincidence from an artificial vertical boundary can be omitted since the moving interval lies strictly inside the larger radius. If \(A>B\) the row is empty. Put \(W_i=\sum_{b<2^{i+1},(b,g)=1}\mu^2(b)/\varphi(b)\). Multiply
\[
 \frac{\rho(g)^2 W_iW_j}{G_-^2}
 \left[\log(B/A)+2.44(A^{-1/2}+B^{-1/2})\right]
 \left[C_1y/(kg)+E_1B\right]
\]
by the near-lobe total area for the \(y\)-coefficient, and by total summed peaks for the intercept, with the normalization in [the direct-row proof](EMPTY_LCM.md). Here \(C_1,E_1\) are exactly its small-prime constants. The signed term subtracted from the Selberg main is estimated on the *same* \(q>x/R\) region by its complete/crossed inverse-moment calculation. Only that small inverse-moment column uses the optional mean-Mertens table. Examples of the direct large-\(q\) slope alone at \(R=1\) are 0, .0048811, .052326, .145570 for \(C=10^6,2\,10^6,3\,10^6,4\,10^6\). The corresponding ordinary normalized main terms are 1.014664, 1.002838, .996048 and .991285 when rounded upward.

## Remaining moduli

The low side uses the prior [squarefree coefficient energies](../../round7/physical/extras/weight_energy.py), the individual-frequency rectangular reciprocal bounds and the [near-lobe derivative method](../../round7/physical/weighted_lobe.py). Use \(J=2^{48}\), 64 dyadic indices, outer inverse-square sums through \(2^{50}\). If a rectangle is cut by \(q\le x/R\), after fixing the true gcd and its coprimality-inversion divisor the cutoff has the form \(v\le V(u)\). Take an integer power of two \(N>z\) and write this prefix as its discrete Fourier transform modulo \(N\). The constant mode is bounded by one in the outer variable. At \(1\le m<N\), the geometric-series numerator is the difference of two outer-variable coefficients of modulus at most one; its denominator is \(2N|\sin(\pi m/N)|\). Hence the total factor is at most \(1+\sum_{m=1}^{N-1}1/(N|\sin(\pi m/N)|)\le 2+\log N<60.918\). All added phases are separated by variable, preserving the rectangular operator input and the derivative input. One can always take the smaller direct trivial bound instead. This method is also valid for the nonnegative Fourier error majorant after retaining its phases.

Full rectangles below the cutoff need no such factor and rectangles above it are discarded. The alternative moves whole crossed rectangles and all large ones to the direct side. It applies only when the gcd groups affected by the cut are singletons, as verified in the program; both the direct main correction and the Fourier inclusion use the same definition.

For the integrated sawtooth approximant, each binary group \(n\le j\le n'\) uses \(2\sum j^{-1}/\pi\) on its phase difference and \(2(n'-n+1)/(J+1)\) for the unsigned Fejér error. The first is bounded by the smaller of its two endpoint bounds and the integrated derivative, whose relative factor is \(\pi n' g_{\rm hi}2^{i+j} e^{c+2r} A_\Sigma/(K z^2 P_\Sigma)\) on inverse-weighted coefficients. Here \(A_\Sigma=I(1-a/\pi)\), \(P_\Sigma=\sin(a)/a+(1+\cos a)/12\). No additional integration-by-parts gain at moving endpoints is assumed. Omitted groups have absolute normalized sum at most \((1+\zeta(2))2^{-50}+2\zeta(2)^2 2^{-64}\) per coefficient; the Fejér constant term is at most \((K_0/G_-)^2/(J+1)\), with \(K_0\) the older full absolute mean. Positive machine sums in a bucket contain fewer than \(2^{26}\) summands, and a relative \(10^{-7}\) guard covers their binary64 operations. Threshold comparisons are checked separately. All tail/constant terms and the actual-multiple counts are evaluated by Arb. The frequency buckets are \(2^{8j}\le n<2^{8(j+1)}\), with \(n=2^{48}\) in the last bucket.

~~~powershell
python -B round8/physical_low/actual_split.py --C 3000000 --mean --exact
python -B round8/physical_low/low_grid.py --mean
python -B round8/physical_low/low_grid.py --mean --rectangles
~~~

The [same-modulus identity](SIGNED_MODULUS.md) proves that the exact charge with absolute values *after* summing each modulus still exceeds .0047443 for \(R=1\), using only the forward first lobe. This strict lower bound distinguishes the sign obstacle from the much larger absolute upper bounds above.
