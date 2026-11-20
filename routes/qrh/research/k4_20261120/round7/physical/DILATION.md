# Dilating the sieve level and sampling reciprocal frequencies

In the [location-sensitive Selberg proof](BILINEAR.md) all the diagonal identities and bilinear decompositions remain valid for \(z=c\sqrt y\), provided \(z<M\). Here the original endpoint Fourier sums are normalized by \(z^2\). The remainder relative to \(y\) must therefore be multiplied by \(c^2\). Put \(a=\frac12\log y+\log c+1.331\); if the resulting relative error is at most \(E\), the sieve gives \(y(1/a+E)\). In a closed length cell \(\ell\le\log y\le u\), its denominator addition in the normalization \(2y/(\log y+\eta)\) is at least
\[
2(\log c+1.331)-\frac{2E a_u^2}{1+E a_u},\qquad a_u=u/2+\log c+1.331 .
\]
For every use of \(c\), the program recalculates both Selberg coefficient bounds and all the changes in the reciprocal frequencies. The positive Vaaler correction at frequency zero is also multiplied by \(c^2\).

## A separated sampling estimate for the bilinear sum

For \(D/2<x\le D,\ F/2<w\le F\), with integer indices, put \(K=A/(DF)>0\). Write \(d_0=\min(1,1/2+1/D)\), \(e_0=\min(1,1/2+1/F)\). If \(|a_x|,|b_w|\le1\), then
\[
\frac{\left|\sum_{x,w}a_x b_w e^{2\pi i A/(xw)}\right|^2}{D^2 F^2}
 \le 1.06\,d_0e_0(1+4K/D)
                  \max\left\{\frac1K,\frac{4(1+1/D)}F\right\}.       \tag{1}
\]
The transposed inequality and the first-derivative estimate in the preceding proof apply to the same blocks.

The sampling points \(\xi_x=D/x\) lie in \([1,2]\) and are separated by \(1/D\), since \(D|x-x'|/(xx')\ge1/D\). The frequencies \(\eta_w=A/(Dw)\) lie in \([K,2K]\) and are separated by \(K/F\). After centering them at \(3K/2\) let \(f(v)=\sum_w b_w\exp(2\pi i(\eta_w-3K/2)v)\). The modulation removed here is absorbed into the coefficients \(a_x\).

Around each \(\xi_x\) take the interval \(I_x\) of length \(1/D\) centered there. The interiors of these intervals are disjoint, and their union lies inside an interval \(I\) of length \(l=1+1/D\). For real differentiable \(g\) one has \(g(\xi_x)\le D\int_{I_x}g+\frac12\int_{I_x}|g'|\): integrate the fundamental theorem of calculus separately on each half of \(I_x\). Apply this to \(g=|f|^2\), sum and use Cauchy to obtain
\[
\sum_x |f(\xi_x)|^2\le D\int_I|f|^2+
                \left(\int_I|f|^2\int_I|f'|^2\right)^{1/2}.
\]
Set \(b=\min(K/F,1/(4l))\), and let \(v_0\) be the center of \(I\). The majorant
\[
W(v)=\frac{\operatorname{sinc}^2(\pi b(v-v_0))}
                {\operatorname{sinc}^2(\pi/8)},\qquad
\operatorname{sinc}t=\frac{\sin t}{t},
\]
is at least one on \(I\). With Fourier frequency in cycles its transform vanishes for \(|\nu|\ge b\), including the endpoints, and its integral is \(1/(b\operatorname{sinc}^2(\pi/8))<1.06/b\). All distinct frequency pairs therefore vanish in \(\int W|f|^2\) and in \(\int W|f'|^2\). Since \(|2\pi(\eta_w-3K/2)|\le\pi K\), the preceding bound is at most
\[
1.06(D+\pi K)\max(F/K,4l)\sum_w|b_w|^2 .
\]
Cauchy in \(x\), the two trivial length bounds, and \(\pi<4\) prove (1). If a block is empty the claim is immediate.

The [reciprocal-sum code](doublesieve.py) applies (1) and its transpose with one-sided endpoints throughout. For \(i\ge j\), \(q=2^{i+j}\), \(A=nt/(gh^2)\), the exact quantity is \(K=ntgq/z^2\). It bounds \(K\) and \(1/K\) independently at the two appropriate rectangle corners. Take the least among these estimates, the first-derivative bound and the trivial bound. The [sieve verifier](dilation.py) charges \(g,h>2^{24}\) and both dyadic tails after block 34 in every Fourier sum, as in the preceding proof. At most \(2^{23}\) positive terms are accumulated per frequency group. The output includes the factor \(1+10^{-7}\), which exceeds the previous floating-point loss bound with \(2^{23}\) in place of \(2^{22}\). The new terms use only normal positive products, divisions, maxima, minima and the final square root. The factor 1.06 also leaves strict slack relative to the proved Fourier constant. Setting \(J\) higher changes both the constant Vaaler term and the full list of nonzero frequencies; the coefficient \(2/(\pi n)+2/(J+1)\) in the preceding proof is summed across every integer up through \(J\).

## Six extended length cells and the fourth powers

Take \(e^{114.98}\le M<M+y\le e^{115.4}\). In the weighted calculation the Fourier coefficient bound is
\[
\frac{2\omega(r)}{\pi n}+\frac{2(1-r)}{J+1},
\qquad r=\frac n{J+1},\qquad \omega(r)=\pi r(1-r)\cot(\pi r)+r .
\]
These are the exact absolute coefficients of the two Vaaler trigonometric polynomials in the preceding proof, with both frequency signs and endpoints included. Arb verifies positivity and sums all coefficients on every frequency group. The following lower bounds on the denominator additions hold on the **entire** indicated cells.

| \(\log y\) | \(c\) | \(J\) | Addition |
|---|---:|---:|---:|
| 83–84 | 5 | 1024 | 3.9465 |
| 84–85 | 6 | 2048 | 4.6404 |
| 85–86 | 7 | 2048 | 4.9876 |
| 86–87 | 7 | 4096 | 5.0939 |
| 87–88 | 5 | 4096 | 5.0089 |
| 88–89 | 5 | 4096 | 4.8274 |

Use these proved additions in the [physical lobe integration](COVER.md), including the older unconditional estimate for every exterior interval whose length or location falls outside these domains. Starting at the previously proved unconditional endpoint \(115.034625\), the closed slabs \([115.034625,115.145]\) and \([115.145,115.1465]\) cost below .999645 and .999924 respectively. They use \(K=H-206000\) and the Gaussian bound for every unverified ordinate; no QRH input enters. The closed slab \([115.145,115.1515]\) costs below .999828 using the certified QRH charge .005937108818 from the [96-window computation](../first_selected/LOW_CONTINUATION.md). The physical theorem on each slab is \(x<p<x+4x^{3/4}\). In particular the integer ranges reach \(3\,175\,940\,738\,573\) without QRH and \(3\,179\,913\,146\,734\) under QRH.

~~~sh
python -B round7/physical/dilated_cover.py --weighted --table
python -B round7/physical/dilated_cover.py --weighted --lo 115.034625 --hi 115.145
python -B round7/physical/dilated_cover.py --weighted --lo 115.145 --hi 115.1465
python -B round7/physical/dilated_cover.py --weighted --lo 115.145 --hi 115.1515 --qrh
~~~
