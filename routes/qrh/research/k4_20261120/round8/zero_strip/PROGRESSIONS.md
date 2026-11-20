# Excluding arithmetic progressions of exceptional zero ordinates

Assume QRH(7/8) and let \(R\ge420071\) exceptional ordinates from the [second true rectangle](STRIP_BOUNDARY.md) be given, with multiplicity. After any ordering of them, for any progression \(t_j=t_0+jd\) with \(0\le d\le5000\),
\[
 \frac1R\sum_j|\gamma_j-t_j|>.00030 .                                  \tag{1}
\]
For \(d<200\), the assertion (1) also follows from the local bounds, as detailed below. If the comparison points form the union of up to **six** arithmetic progressions, each with its own starting point and \(200\le d_i\le5000\), the mean absolute displacement exceeds **.00004**. The lengths of the progressions need not be equal.

In particular, taking the \(1260213\) exceptional points of the [earlier scalar obstruction model](../../round7/qrh_strip/INCREMENT.md) equally spaced in \([T-2\cdot10^9,T]\) has spacing between 1500 and 1600, within (1). This translation-invariant condition excludes this specific dispersed example. It does not assume that general dispersed populations are arithmetic progressions.

## Geometric sums on the prime frequencies

Use (1) in the [strip proof](STRIP_BOUNDARY.md) at \(A=40\). The first prime powers must supply a negative bias of at least \(D=9.49184\) per exceptional zero, with \(V=\sum_p v_p<228.91189\). For an exact progression of length \(N\) and step \(d\), the normalized modulus at \(\log p\) is at most
\[
 \min\left(1,\frac1{N|\sin(d\log p/2)|}\right).
\]
Let \(m\) be a positive integer and \(\varepsilon=1/m\). Declare a prime resonant if \(\|d\log p/(2\pi)\|\le\varepsilon\), distance to the nearest integer being used. Nonresonant primes contribute at most \(V/[N\sin(\pi\varepsilon)]\). If there are \(k\) progressions of total length \(R\), this gives \(kV/[R\sin(\pi\varepsilon)]\) after averaging, even with different steps or translations. For the resonant terms use the uniform bound below for each individual progression, with no dependence on \(N\).

For the head primes \(p\le P\) the verifier covers the entire continuum \(200\le d\le5000\). Put \(\alpha_p=2\pi/\log p\). Resonance confines \(d\) to \([(j-\varepsilon)\alpha_p,(j+\varepsilon)\alpha_p]\) for an integer \(j\ge1\). Enclose \(\alpha_p\) between consecutive multiples of \(10^{-9}\) using Arb. Convert both endpoints outward to overlapping cells of the \(10^{-3}\) mesh in \(d\), by integer division using these two period bounds. Add the integer upper weight \(\lceil10^7v_p\rceil\) throughout these cells, and take the largest sum over the allowed range. The sweep uses integer differences; upper bounds on all intermediate products are checked prior to the multiplications. For each prime, different \(j\)'s have disjoint intervals after gridding; the period rounding enlarges an endpoint by less than \(2\cdot10^{-5}\) at the largest permitted \(j\), and the margin between successive resonances exceeds \(4\cdot10^{-3}\). A bound by the sum of the upper prime weights is additionally checked on the full cumulative array. The multiplicative cell index of a value on the rightmost boundary is included. Different primes may contribute to the same cell and are all added.

For \(p>P\) replace the primes by **all integers** in the logarithmic resonance intervals. For \(u=\log n\), majorize \(v_n\) by \(g(n)=(\log n)n^{-\Theta}(1-(\log n)/A)_+\), decreasing on \(n>P\) throughout its support. On one interval use its integral plus the supremum of \(g\) there. The integral in logarithmic coordinates has density \(h(u)=u e^{(1-\Theta)u}(1-u/A)_+\) for \(u\ge0\), extended by zero to the left. It is unimodal, since \(1/u+1-\Theta-1/(A-u)\) decreases on \((0,A)\).

Write \(\Delta=2\pi/d,\ \Delta_{\max}=2\pi/200\). Each cell of width \(\Delta\) has a central resonant portion of length \(2\varepsilon\Delta\). For the sum of the integrals over those portions use
\[
 2\varepsilon\left(\int_0^A h(u)\,du+
             2\Delta_{\max} A\exp((1-\Theta)A)\right).
\]
Indeed, the full upper rectangles of width \(\Delta\) have total excess bounded by \(\Delta\) times the total variation of \(h\), at most \(2\Delta_{\max}\max h\). For the sum of the extra integer-endpoint costs, use \(u_0=\log P-2\varepsilon\Delta_{\max}\). The earliest left endpoint of a cell's **resonant portion** intersecting \([\log P,A]\) is at least \(u_0\). All subsequent left endpoints are \(\Delta\) apart. The function \(u e^{-\Theta u}\) decreases on this range, so the total extra charge is at most
\[
 e^{-\Theta u_0}\left[u_0+\frac{5000}{2\pi}
              \left(\frac{u_0}{\Theta}+\frac1{\Theta^2}\right)\right].
\]

| Number of progressions | \(P,m\) | Head | Nonresonant | Tail integrals | Integer-endpoint cost |
|---:|---|---:|---:|---:|---:|
| 1 | 9000, 8192 | .577014 | 1.420973 | 1.504314 | 3.235034 |
| 6 | 30000, 4000 | .589261 | 4.163007 | 3.080835 | 1.260696 |

Passing from the comparison points to the true ordinates adds at most \(AVR^{-1}\sum_j|\gamma_j-t_j|\) to the normalized weighted sum of the prime phases, since \(p\le e^A\) and \(|e^{ix}-e^{iy}|\le |x-y|\). Subtracting the table entries from the lower bias, with the full Arb enclosures, gives the allowable displacement thresholds **.0003008270** and **.0000434721**.

The comparison is also stable under arbitrary modifications of a minority of points. Changing one ordinate changes the total prime sum by at most \(2V\), independently of the change in height. If just \(J\) coordinates differ from an exact model and its upper bias is \(B_{\rm model}\) per zero, then
\[
  J\ \ge\ \frac{R(D-B_{\rm model})}{2V}.
\]
At the minimum failing population this requires at least **2528** arbitrary changes to one progression, or **366** to the union of six, throughout the scanned spacing range. For larger populations the same certified fractions of \(R\) apply.

For a single progression and \(d<200\), a mean displacement at most .00030 implies that at least \(0.9997R\) points have displacement at most one. These all lie in an interval of width at most \(200R+2\), intersected with \([H,T]\). When \(420071\le R\le500000\), this width is less than \(116000000\) and the number of such points would exceed the proven cap 256862. When \(R>500000\), partition the interval into pieces of width at most \(116000000\). Their common upper bound gives at most \(256862[(200R+2)/116000000+1]<0.9997R\) points. Short subintervals of the actual rectangle can be extended to full width in applying the cap.

~~~sh
python -B round8/zero_strip/progressions.py
~~~
