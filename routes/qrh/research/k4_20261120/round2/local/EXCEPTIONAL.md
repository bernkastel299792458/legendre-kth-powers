# Explicit counts of possible exceptions among fourth-power gaps

Let \(B_L\) be the integers \(n\) for which
\([4\log n,4\log(n+1)]\subset[L,L+1]\). Let \(E_L\) count those
\(n\in B_L\) for which \((n^4,(n+1)^4)\) contains no prime.
The argument below bounds \(E_L/\#B_L\) for every real \(114.96\le L\le305\).
It gives a count, without determining the individual exceptional candidates.

Both versions assume QRH(7/8) and RH verified to \(H=3\cdot10^{12}\).
The CS column uses Corollary 1 of the Chourasiya–Simonič v2 preprint.
The K5 column instead accepts the **absolute weighted zero-sum estimate**
from §3, §6b–e of Claude's local, unpublished
\(\texttt{qrh_k3k4_claude/k5/MAIN_K5.md}\).
The assertion that fifth-power intervals contain primes alone does not imply
that estimate. The K5 input includes its mollifier coefficient computations,
its Möbius sum inputs and its floating-library hypothesis ELEM. We have not
independently rebuilt those inputs here. References for the published
finite-height RH and the local zero count are [Platt–Trudgian, Theorem 1](https://arxiv.org/pdf/2004.09765)
and [Carneiro–Milinovich–Soundararajan (CMS), Lemma 9](https://arxiv.org/pdf/1708.04122).
The density source is [CS v2, Corollary 1 and the bounds immediately following it](https://arxiv.org/html/2507.15184v2#S1).

| Block start \(L\) | Upper bound for \(E_L/\#B_L\), CS | Upper bound for \(E_L/\#B_L\), K5 |
|---:|---:|---:|
| 114.96 | 0.282 | 0.01204 |
| 116 | 0.244 | 0.01102 |
| 120 | 0.140 | 0.00782 |
| 130 | 0.0342 | 0.00331 |
| 150 | 0.00195 | 0.000583 |
| 200 | \(1.22\cdot10^{-6}\) | \(7.11\cdot10^{-6}\) |
| 250 | \(6.25\cdot10^{-10}\) | \(8.15\cdot10^{-8}\) |
| 304 | \(1.52\cdot10^{-13}\) | \(6.26\cdot10^{-10}\) |
| every \(114.96\le L\le305\) | 0.314 | 0.01415 |

Over **all** integers \(114.96<4\log n<305\), the CS version permits fewer
than \(4.811\cdot10^{20}\) exceptions out of more than \(1.303\cdot10^{33}\)
integers. Thus under the CS version's assumptions the aggregate proportion
is below \(3.70\cdot10^{-13}\). The K5 version alone gives fewer than
\(1.223\cdot10^{24}\) possible exceptions over that same entire range.
These aggregate percentages weight blocks by the number of integers
they contain, so they are substantially smaller than the percentages in
the first blocks.

## 1. From each empty gap to an interval of centers

Set \(M=e^{(L+1)/4},\ d=1/M,\ T_*=2M\), and \(f(v)=(1-|v|/d)_+\).
For \(c\in[L,L+1]\) put
\[
 A(c)=d^{-1}\sum_m\frac{\Lambda(m)}m f(\log m-c).
\]
The continuous piecewise linear weight gives the explicit formula
\[
 A(c)=1-\sum_\rho e^{(\rho-1)c}K_d(\rho-1)-\tau(c),\qquad
 K_d(z)=\left(\frac{\sinh(dz/2)}{dz/2}\right)^2.                    \tag{1}
\]
Indeed the pole integrates to 1 after changing variables to \(u=\log m\),
and the transform of the tent against \(e^{zu}\) is
\(d e^{zc}K_d(z)\). The constant in the classical explicit formula for
\(\psi\) disappears upon differentiation. The trivial-zero density gives
\(0<\tau(c)\le e^{-3(c-d)}/(1-e^{-2(c-d)})\). Equivalently one can first
apply the integrated explicit formula to a smooth approximation and take
its limit. The zero series in (1) is absolutely convergent since
\[
 |K_d(\rho-1)|\le e^d\min(1,(T_*/|\gamma|)^2).
\]
The first bound follows by the integral formula for \(\sinh z/z\), the
second from \(|\sinh(x+iy)|\le\cosh x\).

The contribution of \(|\gamma|\le H\) to the absolute sum is bounded by
\(2H\log H\,e^{d-L/2}\) using finite RH. If the tent is contained in
the closed log interval of a failing \(n\), the endpoints have zero tent
weight if they occur at its support boundary. Only higher prime powers
can contribute, and the elementary
\(\psi(y)-\theta(y)\le\sqrt y(\log y)^2/(2\log2)\) gives
\[
 A(c)\le\frac{(L+1+d)^2}{2d\log2}\,e^{3d/2-L/2}.
\]
Denote by \(D\) the number 1 minus these three uniform errors (trivial
zeros, low zeros and powers). Write \(Z(c)\) for the zero sum restricted
to \(|\gamma|>H\). Every failing gap has log length
\(4\log(1+1/n)\ge4/(n+1)\ge4/M\), and therefore supplies a subinterval
of centers of length at least \(2/M\) with \(|Z(c)|\ge D\). These
subintervals are disjoint. Consequently
\[
 \frac{E_L}{\# B_L}\le
 \frac{\int_L^{L+1}|Z(c)|^2\,dc}
 {2(1-e^{-1/4}-2/M)D^2},                                         \tag{2}
\]
because \(\#B_L\ge M(1-e^{-1/4})-2\).

## 2. A mean square over the locations of the fourth-power gaps

For ordinates \(|\gamma|>H\) with multiplicity and fixed coefficients \(a_\rho\),
\[
 \int_0^1\left|\sum a_\rho e^{i\gamma s}\right|^2ds
 \le C\sum_\rho |a_\rho|^2\log|\gamma|,
 \qquad C=\frac{\pi}{2\sin^2(1)}\,1.16.                            \tag{3}
\]
To prove this use the nonnegative majorant
\(\operatorname{sinc}^2(2(s-1/2))/\sin^2(1)\) for the indicator
of \([0,1]\), where \(\operatorname{sinc}(t)=\sin t/t\). The absolute
value of its angular Fourier transform is
\(\pi(1-|\xi|/4)_+/(2\sin^2(1))\).
In the resulting double sum apply \(2|a_i a_j|\le|a_i|^2+|a_j|^2\).
Each row has frequencies of one sign, since its radius is 4 and \(H>4\).
For \(v=|\gamma|\ge H\) its triangular row sum is bounded by
\[
 \frac14\int_0^4[N(v+w)-N(v-w)]\,dw
 \le(2/\pi+0.3)\log(v+4)+6\le1.16\log v .
\]
Coincidences at interval endpoints do not affect the integral. CMS Lemma 9
bounds the error in \(N(t)\) about its usual main term by \(0.15\log t+3\);
the difference of the two main terms is at most
\((w/\pi)\log(v+4)\). For the final comparison use
\(\log(v+4)/\log v=1+\log(1+4/v)/\log v\), decreasing for \(v\ge H\).
This proves (3) first for finite sums and then for (1) by truncation.

If the real parts in a group lie in \([b-\delta,b+\delta]\), expand
\(e^{(\beta-1)s}=e^{(b-1)s}\sum_{j\ge0}(\beta-b)^j s^j/j!\).
The separated factors \(e^{(b-1)s}s^j\) have modulus at most 1 on
\([0,1]\). Minkowski and (3) therefore cost at most \(e^\delta\)
in the \(L^2\) norm. Split at \(\beta=3/4\); the low group lies in
\([1/8,7/8]\) by symmetry and QRH, and the high group in \([3/4,7/8]\).
Let \(S_0,S_1\) bound for each group the **positive-height** sum
\[
 \sum_{\gamma>H} e^{2(\beta-1)L}\log\gamma\,
                 k(\gamma),\qquad k(v)=\min(1,(T_*/v)^4).
\]
Conjugation doubles each coefficient energy before taking its square root.
Hence
\[
 \int_L^{L+1}|Z(c)|^2dc
 \le 2Ce^{2d}\big(e^{3/8}\sqrt{S_0}+e^{1/16}\sqrt{S_1}\big)^2.    \tag{4}
\]
All differences of ordinates in (3) were counted for the entire groups.
No simplicity, pair-correlation estimate or random-phase hypothesis enters.

## 3. Computing the two coefficient energies

For \(u=\log T_*\), denote
\[
 I_{p,q}=\frac{4T_*^p u^q}{4-p-q/u}.
\]
This bounds \(\int_{T_*}^\infty t^p(\log t)^q(-dk(t))\) because, with
\(t=T_* y\), \((1+\log(y)/u)^q\le y^{q/u}\). All denominators are positive
in the certificate. A cumulative bound for weights up to \(t\) may be
multiplied by \(\log t\) to bound those weights times \(\log\gamma\), then
integrated against \(-dk\), which includes the full infinite tail by Tonelli.
As \(N(t)\le t\log t\) for \(t\ge H\), this gives
\(S_0=e^{-L/2}I_{1,2}\).

**CS bound.** Let \(h=1/512,\ s_j=jh,\ 384\le j<448\), and
\[
 p(s)=3(1-s)/(2-s),\quad
 J(s)=21.77I_{p(s),3+p(s)}+8.290 I_{0,3}+147 I_{0,2}.
\]
By CS Corollary 1, \(J(s)\) bounds the logarithmically weighted counts
for the strip \(\beta\ge s\) after integrating against \(-dk\).
The extra factor of \(\log t\) is included in each exponent.
Put \(w(s)=e^{2(s-1)L}\). A layer-cake bound is
\[
 S_1=w(3/4)J(3/4)
       +\sum_{j=384}^{447}(w(s_{j+1})-w(s_j))J(s_j).              \tag{5}
\]
The counting function decreases in \(s\), justifying the left endpoints.

**K5 bound.** Set \(\lambda=5\log(35T_*/16)\),
\(q=1+e^{\lambda/5}/5\), and
\(g_q(t)=\min(1,16q/(7t),256q^2/(7t^2))\).
The specific input used here is
\[
 2\sum_{\gamma>H} e^{(\beta-1)\lambda}g_q(\gamma)<1.
\]
It follows directly from the accepted positive upper budget in §3 of
Claude's K5 manuscript, applied on its certified cell containing \(\lambda\):
the cell's left endpoint enlarges the weights and its right endpoint
enlarges \(g_q\). All the additional deductions in that budget are positive.
The arguments needed here lie between 138.218 and 800. We use the two
corrected H3-free certificates up to 362 and the large certificate thereafter.

By construction \(16q/7>T_*\) and \(256q^2/7> T_*^2\), so
\(\log\gamma\, k(\gamma)\le(\log T_*) g_q(\gamma)\).
For \(\gamma>T_*\) use \(\log(T_*y)\le y^2\log T_*\), \(y=\gamma/T_*\).
Also \(2L>\lambda\), hence
\[
 S_1=\tfrac12\log(T_*)e^{-(2L-\lambda)/8}                          \tag{6}
\]
is sufficient. This use of the fifth-power zero budget works because the
fourth-power location average squares the zero amplitudes.

## 4. Numerical coverage and limitations

Run the accompanying [check_exceptional.py](check_exceptional.py) in
Python with python-flint. The table uses 160-bit Arb. For a closed cell
\([l,r]\) of possible \(L\), take \(M_{\min}=e^{(l+1)/4}\),
\(M_{\max}=e^{(r+1)/4}\), maximizing \(d,T_*\) separately and using the
smaller \(M\) in the denominator of (2). Each \(I_{p,q}\) increases with
the scale in its defining integral; the proof uses the integral at the
upper scale followed by the displayed analytic bound. The weights in (5)
decrease with \(L\): for differences this follows by integrating
\(2L e^{2(s-1)L}\) over \([s_j,s_{j+1}]\). In (6) use \(2l\) and the
upper \(\lambda\). The initial cell \([114.96,115]\) and subsequent unit
cells through 305 cover all real starts. In particular the table does not
interpolate between point samples.

To obtain the aggregate count, cover the range by the unit log blocks
starting at 114.96 and at \(115,116,\ldots,304\). In each multiply the
pointwise proportion bound by \(e^{L/4}(e^{1/4}-1)+1\), an upper bound
for \(\#B_L\). Apart from gaps crossing a block boundary this covers every
integer in question. At most one disjoint gap can straddle each boundary,
and adding 192 safely includes all of them (also the gap at 305). Double
counting in the overlap of the first two intervals only increases the sum.
The number of eligible integers exceeds \(e^{305/4}-e^{114.96/4}-1\).

At \(L=120\), \(\#B_L\) exceeds \(3\cdot 10^{12}\), so even the smaller
displayed bound permits many exceptions. A pointwise route would need to
force insufficient energy on the much shorter location window of a *given*
empty gap, or to use additional arithmetic information to identify and
eliminate the candidates.

One obstruction to upgrading the earlier finite-height, uniform exterior
sieve by combining more bandlimited tests can be exhibited explicitly.
For \(T>H,\ \alpha=Td/\pi<1\), define a continuous-density model of period
\(2\pi/T\) with value zero in every translate of \((-d,d)\) and value
\((1-\alpha)^{-1}\) elsewhere. It has mean 1 and matches the constant
density against every Schwartz test with angular spectrum in \([-H,H]\),
including all translates and simultaneous tests. Here \(d\) in the
obstruction is the actual target half-width
\(\tfrac12\log(1+4e^{-L/4})\), distinct from the smaller tent used in
(1). As \(T\downarrow H\), the cap tends to
\((1-Hd/\pi)^{-1}\), approximately 1.94478504 at \(L=116\) and
1.21760773 at \(L=120\). Even a uniform cap of 2 admits such a model at
both starts. This exact Fourier statement concerns an auxiliary real
measure; it claims no realization on the primes or zeta zeros. In contrast,
the location-averaged calculation above uses the high-zero positions through
their local counts as well as the \(\beta\)-weighted energy.
