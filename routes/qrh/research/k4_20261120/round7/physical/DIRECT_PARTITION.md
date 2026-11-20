# Replacing the exterior lobe charges in the original budget

Take the notation of [the explicit formula](../../round2/local/EDGE.md), and assume the target interval contains no prime. Its original arithmetic bound near the center has the form \(s\,I(1-a/\pi)+bP_{64}+E_0\), with \(s,b\) the slope and intercept of the reference tangent, \(P_{64}\) the sum of the original 64 two-sided peak caps plus the \(j>64\) integral bound, and \(E_0\) the 256-cell correction for the first lobe. For \(J\ge1\) with \(2\pi(J+2)<Kr\), let \(A_1\) be the area of the first positive exterior lobe on one side, and let \(A_2\) sum the one-sided areas of lobes \(1,\ldots,J\). With their separately certified two-sided Selberg charges \(s_1A_1+e_1,s_2A_2+e_2\), the following is a valid replacement:
\[
 sI(1-a/\pi)+(s_1-2s)A_1+e_1+(s_2-2s)A_2+e_2+
 b(1+\cos a)/(2\pi^2J).
\]
Every removed lobe is complete and lies in the original near-center domain. The remaining positive exterior area on both sides is at most \(I(1-a/\pi)-2A_1-2A_2\). Its peak sum is at most \((1+\cos a)/(2\pi^2J)\), since each peak on one side is bounded by \((1+\cos a)/(4\pi^2 j^2)\). These are the exact terms to which the original reference tangent applies, even if another lobe runs through the cutoff. All Gaussian, archimedean, pole, prime-power and other far terms stay in the original formula. For a freshly computed near-height charge the same Gaussian tail beyond \(H+(K-H)+128Q\) is evaluated explicitly. The first and secondary positive errors use the [unit Selberg estimates](UNIT_SIEVE.md). The new calculation needs no interpolated denominator additions for individual lobe lengths.

For \(115.402\le L\le115.412\) the direct replacement with \(K-H=16\cdot10^9\), 64 secondary lobe pairs, primorial 30 and the published-height and QRH inputs gives full cost between 1.0023854 and 1.0023856. Extending the replacement alone has not certified that entire slab.

## A second sampling majorant

For every \(b>0\) let \(R\) majorize the indicator of \([1,2]\) on the line, be nonnegative there, have exponential type \(2\pi b\), and have integral \(1+1/b\). The Beurling–Selberg interval majorant has these properties; at an endpoint continuity gives the interior one-sided bound. Rescaling gives arbitrary \(b\). Krein's nonnegative entire-function factorization gives \(R=UU^*\) with \(U\) of type at most \(\pi b\). On the real axis \(|U|\ge1\) on the target interval and \(\|U\|_2^2=1+1/b\). Its Fourier support has width at most \(b\) by Paley–Wiener. [Carneiro, Chandee and Milinovich, Lemma 2](https://arxiv.org/pdf/1503.00955) · [Carneiro, Chandee, Littmann and Milinovich, factorization on p. 10](https://arxiv.org/pdf/1406.5462)

On one frequency class, let \(\delta\) be its guaranteed separation and choose \(b=\min(B,\delta)\). The cross terms in \(\int |U(t)\sum_j c_j e^{2\pi i\eta_jt}|^2dt\) vanish, including ties at the edge of the continuous Fourier transform of \(R\). Its value is \((1+1/b)\sum_j|c_j|^2\). The earlier sampling inequality applies to the product, whose frequency span is at most the original span plus \(B\). In one of \(k\) classes of separation \(vK_0/F\), the resulting frequency factor, after Cauchy over the classes, is at most
\[
 k/F+\max\{k/(vK_0),\,k/(BF)\}.
\]
Multiply by the same outer sampling factor as in the [earlier proof](extras/WEIGHT_ENERGY.md). The bandwidths \(1,4,16,128,1024,\sqrt{D+K}\) may be tried independently: any positive choice gives the inequality. All scale-dependent numerator and denominator bounds still take opposite rectangle corners. The option \(\verb|--majorant|\) adds this competitor to the sine majorants for each arithmetic and rational frequency class. The enlarged positive-term estimates use the existing \(1+10^{-7}\) inflation.

~~~powershell
python -B round7/physical/direct_partition.py --lo 115.402 --hi 115.412 --qrh
~~~

## Exact coincidence corrections

For a fixed surviving harmonic \(n\in[N,J]\), write its ratio to a second harmonic as \(n'/n=a/d\) in lowest terms. Equality of two rational frequencies \(n/w=n'/w'\) forces \(d\mid n,w\), \(w'=aw/d\), and \((ad,P)=1\). The factor \(d=1\) contributes just the original pair because \(J<2N\) on every nonsingleton group. Dropping the requirement that \(w'\) also belongs to its original dyadic interval, the number of extra representations is at most
\[
 \sum_{\substack{d\mid(n,w),\,d>1\\ (d,P)=1}}
 C_{n,d},\qquad
 C_{n,d}=\#\{N/(n/d)\le a\le J/(n/d):(a,dP)=1\}.
\]
The term corresponding to the original representation can use the exact squared row energy. A divisor \(d>1\) costs at most its squared row supremum times \(F/d\), with the unit-density improvement for \(w/d\) recorded in [the residue proof](UNIT_SIEVE.md). This treatment uses the signs only before taking squared masses in Cauchy's inequality.

The three choices of harmonic coefficients are \(n^{-p}\), \(p=0,1,2\), restricted to \((n,s)=1\), with \(s\mid P\). The new correction, before multiplying the squared row supremum and its unit density factor, is bounded by
\[
 \frac{1}{(\sum n^{-p})^2}\sum_{(n,s)=1}n^{-2p}
       \sum_{d\mid n,\,d>1,\,(d,P)=1} C_{n,d}/d.
\]
[The computation](rational_collisions.py) uses exact inclusion–exclusion in each numerator interval for \(J\le8192\). For larger \(J\), write \(n=db,n'=ab\), \(a\ne d\). Both \(a,d\) are units of the even \(P\), whence \(b\le(J-N)/2\). On each \(b\), if \(D_b\) counts the units in \([\lceil N/b\rceil,\lfloor J/b\rfloor]\), the unweighted inner sum is at most \(D_b(D_b-1)/\lceil N/b\rceil\). Count the first 512 rows exactly. On the rest put \(h=J-N\), use \(D_b\le\eta h/b+\Delta\) and \(D_b-1\le h/(2b)\) whenever \(D_b>0\). The smaller of these product bounds and \(D_b(D_b-1)\le(\eta h/b+\Delta)(\eta h/b+\Delta-1)\) can be summed on each dyadic section of the \(b\) range. The known real-endpoint discrepancy is at least one for these wheels. The count, first moment and harmonic moment over \(b\) coprime to \(s\) use inclusion–exclusion; the latter is a digamma difference. For normalization use \(n^{-2p}/(\sum n^{-p})^2\le(J/N)^{2p}/\#\{(n,s)=1\}^2\). The code compares both complete squared-mass bounds for each block and orientation.

## Reusing a translated height computation

The translated fourth moment, centered short core, and circular horizontal bounds use [the selected height-window estimates](../first_selected/SELECTED.md). In [near_height.py](../first_selected/near_height.py), \(R=D/2,\ U=\log R\), the right half-integral is \(U\) times the frequency-local constant for \(Q=2310\). A height translation multiplies the Dirichlet coefficients by unimodular phases in its folded mean; the coefficient energies are computed before translation. The Jacobian and the factor \(1/\pi\) match those in the earlier [translated hinge formula](../../round5/low/NARROW_COVER.md). The origin and the two horizontal sides are kept for every real-part node. At small widths the established modulus-six estimate is always available. Disjoint log-height increments with decreasing positive weights are summed as in [the low-height replay](../../round6/first_rect/LOW_JOIN.md).

At the reference \([115.402,115.412]\) the computed charges are below .005136954129 for \(K-H=16\cdot10^9\) with eight panels, .008863230454 for \(24\cdot10^9\) with six, and .012974040787 for \(32\cdot10^9\) with six. For another pair \(l,h\) at the same \(K\), put \(l_0=115.402,\ a_0=a(115.412),\ a=a(h),\ v=a_0(K-H)/K\). For \(0\le y_0\le v<\pi/2\), \(\sin((a/a_0)y_0)\le(a/a_0)(v/\sin v)\sin y_0\) whenever the new argument is nonnegative. The same transfer dominates the additive term proportional to \(a\); clipped new weights only decrease. Beyond \(K\) the positive-part argument is zero. The old cap is unclipped throughout, as checked explicitly. Multiply by \(\sin a_0/\sin a\) and by \(\max(e^{-(l-l_0)/8},e^{-(l-l_0)})\), which handles \(0\le\beta\le7/8\). This bounds the true finite charge by the old certified charge times the resulting ratio. The Gaussian remainder is independently integrated in the new slab.

~~~powershell
python -B round7/first_selected/near_height.py --lo 115.402 --hi 115.412 --size 16000000000 --panels 8
python -B round7/first_selected/near_height.py --lo 115.402 --hi 115.412 --size 24000000000 --panels 6
python -B round7/first_selected/near_height.py --lo 115.402 --hi 115.412 --size 32000000000 --panels 6
~~~

## Two endpoint refinements

Write \(F(w)=g(a+w)\), \(p=-F'\) on \([0,b]\). Distributing the nonnegative measure \(p(w)\,dw\) between the factors \(q_1=1-(w/b)^m\) and \(q_2=(w/b)^m\) permits separate choices of sieve level and inward averaging width. For each component use cap \(\int q_i p\), area \(\int wq_i p\), and moving-endpoint variation \(|q_ip|_0+|q_ip|_b+\int|(q_ip)'|+\int q_ip/K\). The two physical prime sums add because \(q_1+q_2=1\). From the sine integral, \(|F^{(k)}|\le1/((k+1)(k+2))\). Thus \(|(q_ip)''|\le m(m-1)/(6b^2)+m/(6b)+1/20\), with \(|(q_ip)'|\le m/(6b)+1/12\). [The component enclosure](endpoint_density.py) applies the composite midpoint error to the cap and area and uses the same second derivative for the variation. Three trials on the complete slab \([115.402,115.410]\) gave upper bounds above one.

For a smooth moving density \(p\), let \(B_1=|p(0)|+|p(b)|\). Let \(B_2=|p'(0)|+|p'(b)|+B_1/K+\int_0^b(|p''|+3|p'|/K+2|p|/K^2)\). Put \(t(w)=e^{c\pm(a+w)/K}\), \(Z=m_* K e^{r-l}/(2\pi n)\) for a reciprocal-modulus block. Two integrations by parts give an alternative absolute cost proportional to \(ZB_1+Z^2B_2\). Both powers of the ratio of the true modulus to \(m_*\) factor into contractions of the two original coefficient rows. In the squared term use \(1/n\le1/N\) on a grouped band starting at \(N\). This proof also applies to the signed derivative on each secondary lobe with both its endpoints. The [variation routine](lobe_variation.py) evaluates the second and third derivatives on interval panels there. The ordinary one-integration bound and the lower-frequency difference estimate both remain admissible on each individual block.

The rational-coincidence calculation gives full cost below .999920 on \([115.384,115.389]\) with unrestricted high zeros, and below .999302 with QRH on \([115.402,115.404]\). The second integration by parts gives a further overlapping QRH slab \([115.402,115.405]\), with cost below .999769. The spectral interval majorant and the exact coincidence treatment are separate choices in the commands.

~~~powershell
python -B round7/physical/direct_partition.py --lo 115.384 --hi 115.389 --ratio 98 --secondary-ratio 123 --inside .0014 --collisions --check
python -B round7/physical/direct_partition.py --lo 115.402 --hi 115.404 --ratio 148 --lobes 128 --qrh --collisions --check
python -B round7/physical/direct_partition.py --lo 115.402 --hi 115.405 --ratio 143 --lobes 96 --qrh --majorant --twice-moving --check
~~~

The same near-height reference on \([115.402,115.412]\) gives upper bounds .021994422840 at \(48\cdot10^9\) with eight panels, .030243530145 at \(60\cdot10^9\) with six, and .061018556407 at \(100\cdot10^9\) with six. Reuse the command above with those values of size and panels. The mixed-spectrum calculation in [COMPANION_KERNEL.md](COMPANION_KERNEL.md) also supplies an independent ten-panel evaluation for its \(100\cdot10^9\) test.
