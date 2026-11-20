# Moving the zeros of the spatial test

Let \(g_b(u)=(\cos b-\cos u)/(u^2-b^2)\) with its entire continuation. For positive weights \(e_j\) choose \(b_j=2\pi m_j+s_j a\), \(s_j\in\{-1,1\}\), \(m_j\ge1\), with all \(b_j\) distinct. Set
\[
 c=1+a\sum_j s_je_j/b_j,\qquad r=c-\sum_j e_j>0,\qquad
 f=cg_a-\sum_j e_jg_{b_j}.
\]
The mass of \(f\) is exactly \(I=\pi\sin a/a\), since \(\int g_b=\pi\sin b/b\). All summands have bandwidth one in the angular convention of [the explicit formula](../../lower/PROOF.md). On setting \(x=u^2\) their ratio to the old test is
\[
 R(x)=c-\sum_j e_j(x-a^2)/(x-b_j^2).
\]
Each summand in \(R'(x)\) is \(e_j(b_j^2-a^2)/(x-b_j^2)^2>0\). At a pole the ratio jumps from positive to negative infinity. Between consecutive poles there is one new zero, and there is one above the final pole because \(R\) tends to \(r>0\). With \(S=\sum_j e_j(b_j^2-a^2)\), the final zero is below \(b_{\max}^2+2S/r\) in the \(x\) coordinate. [The enclosure](companion_shape.py) proves both endpoint signs and bisects every interval. Remove the chosen \(b_j\) from the list of positive spatial zeros and insert the new square roots \(d_j\). The numerical ordering is independently checked by rigorous strict comparisons, including every unmoved zero and the unperturbed cutoff at \(2\pi(J+1)-a\). Starting with a positive value at \(a\), the signs then alternate through this ordered list. Beyond the final altered zero the ratio is positive and at most \(r\).

For any such perturbation, the integral of \(f\) against the periodic indicator \(1_{\{\cos u<\cos a\}}\) is still \((1-a/\pi)I\), by constant periodization and the vanishing of the Fourier transform at both band edges. The increase in the true positive exterior area is the integral of \(|f|\) over the symmetric difference of the old and new positive sets outside the target. For a shift that stops before the next original zero, this is twice the sum of the absolute integrals between each original endpoint and its replacement. This supplies a quick numerical design criterion. The full proof evaluates the actual positive lobes even when an endpoint moves past an unshifted zero.

The canonical product of the two sinc functions for \(g_a\) is a product over pairs of its real zeros \(\pm u_i\) of factors \(1-u^2/u_i^2\), with a positive constant. The identity \(R(x)=r\prod_j(x-d_j^2)/(x-b_j^2)\) replaces exactly the designated zero pairs. The resulting product converges normally since \(\sum_i u_i^{-2}<\infty\). On the first positive interval before its first zero this gives strict decrease for \(u>0\). Between any two consecutive zeros the second derivative of \(\log|f|\) is the negative sum of their reciprocal squared distances, over both signs of every zero. Hence every complete positive lobe has exactly one peak. The code brackets that peak by the sign of \(f'\) and allows the residual bracket radius times \((c+\sum e_j)/6\), an upper bound for \(|f'|\).

Use the [first-lobe Selberg proof](WEIGHTED_LOBE.md) with cap \(f(a)\), its integral as the area, and the sum of the endpoint derivative moduli, \(\int |f''|\), and \(f(a)/K\) as the moving-endpoint variation. For each later positive interval let \(P\) bound its unique peak and let \(2C=|f'(u_l)|+|f'(u_r)|+\int|f''|+2P/K\). The signed measure \(f'\,du\) has total mass zero and variation at most \(2P\). Its integrated primitive is the nonnegative lobe. Thus the three secondary Selberg estimates apply to its actual area and to \(P,C\). Interval enclosures cover every shifted endpoint. At a removable pole the numerator divided by \(u-b\) equals \(\int_0^1\sin(b+t(u-b))\,dt\). Evaluate its derivatives and Taylor remainders before dividing by \(u+b\).

Every area can be calculated at its two true endpoints. Set \(\operatorname{Cin}(x)=\int_0^x(1-\cos t)\,dt/t\) and \(\operatorname{Si}(x)=\int_0^x\sin t\,dt/t\). Partial fractions give the following primitive of \(g_b\),
\[
 \frac{\cos b[\operatorname{Cin}(u-b)-\operatorname{Cin}(u+b)]
 +\sin b[\operatorname{Si}(u-b)+\operatorname{Si}(u+b)]}{2b}.
\]
For small arguments use the power series for Cin. Elsewhere it equals \(\gamma+\log|x|-\operatorname{Ci}(|x|)\). The remaining integral of \(|f''|\) is bounded above using interval panels.

For \(j>J\) past all the shifted intervals, one side of the old exterior area is at most \([2(\pi-a)\cos a+2\sin a]/(4\pi^2 J)\). Integrate the numerator on each old positive lobe and use the denominator bound \(4\pi^2j^2\). The two-sided old peak sum is at most \((1+\cos a)/(2\pi^2J)\). One may therefore apply the old affine tangent to \(r g_a^+\) on those components. The remaining log annulus beyond the near-center region is also bounded by the old positive test whenever \(r\le1\), or by twice its cost whenever \(r\le2\).

At unverified heights write \(x=(1-|t|/K)_+\). The quotient of the two real undamped spectra on their support is
\[
 c-\sum_j e_j\operatorname{sinc}(b_jx)/\operatorname{sinc}(ax).
\]
For \(H<\gamma\le K+128Q\) and Gaussian displacement \(|X|\le128Q\), one only needs \(0\le x\le(K-H+128Q)/K\). The numerical proof bounds the quotient in modulus on that entire interval. Multiply the previous positive near-height charge by this supremum. Complex Gaussian convolution contributes the same factor \(e^{1/(16Q^2)}\) as before. The discarded Gaussian event has probability at most \(e^{-128^2/4}\); the finite window contains at most \((K+128Q)^2\) positive zeros. The remote range uses the previous Gaussian density bound with the spatial spectral \(L^1\) factor changed from \(2\pi g_a(0)\) to at most \(2\pi(cg_a(0)+\sum e_j/b_j)\). Together these remainders are below \((100+20K/Q)(K+128Q)^2e^{-128^2/4}\) in the checked parameter range.

For the pole, \(u^2|g_b(u)|\le4b\) on \(|u|\le2b\), using \(|g_b|\le1/b\). Outside, the rational form gives \(8/3\). All companion \(b>1\). The old pole loss therefore incurs a multiplier at most \(c+\sum e_j b_j/2\). The bounds for prime powers, the gamma term and the Gaussian spatial tail use the same \(L^1\) or pointwise factor as above. The verified-height supremum of the spectrum costs at most \(\pi(c/a+\sum e_j/b_j)/K\). [The complete calculation](companion_cover.py) verifies that every factor except the separately corrected pole is within twice the original allowance. All rows use the near-height bounds with the listed QRH and finite-height analytic inputs.

## Closed interval and numerical replay

With one displaced zero in each of the first 24 periods, all on the \(2\pi j-a\) side, total companion weight \(3/10\), and \(K-H=32\cdot10^9\), the complete upper bound on \([115.404,115.408]\) is below **0.999811047751076**. The first and remaining explicitly integrated lobe charges are below .892887 and .096379 respectively. The high-ordinate charge is below .0094130, using a bound .724653 on the ratio of the two spectra throughout the relevant edge region. This joins the [previous physical comparison](DIRECT_PARTITION.md).

~~~powershell
python -B round7/physical/companion_cover.py --lo 115.404 --hi 115.408 --size 32000000000 --count 24 --weight .3 --mesh 96 --check
~~~

A finer alternative integrates the mixed spectrum against a fixed table of cumulative positive-ordinate bounds. On \(0\le x\le(K-H)/K\) its normalized profile is
\[
V(x)=\frac{a}{\sin a}\left(c\sin(ax)/a-\sum_j e_j\sin(b_jx)/b_j\right).
\]
The check \(c\cos(a(K-H)/K)>\sum_j e_j\) implies \(V'\ge0\) throughout this range. Thus the left endpoints of the consecutive height bands give a decreasing majorant. For the smoothed extension, the complex Gaussian multiplier has expectation one; subtracting the unperturbed value costs at most \(e^{1/(16Q^2)}2Q(c+\sum_j e_j)a/(K\sqrt\pi\sin a)\) times the total weighted count. Above the last table height keep the remote tail already charged. When the physical parameter moves from the table's reference \(L_0\) to \(L\), each weight \(e^{-(L-L_0)(1-\beta)}\) costs at most \(\exp(\max\{-(L-L_0),-(L-L_0)/8\})\). [Cumulative table and Abel differences](../first_selected/companion_heights.py)

## A common sieve bound and the extended interval

Freeze the Selberg level \(z=\lambda\exp((l_0-\log K)/2)\) throughout an outer interval \([l_0,h_0]\). Use the denominator for this same frozen level. Write \(P,C,A\) for the cap, moving-endpoint variation and area, including the inward extension \(P\epsilon/2\) on the first lobe. After multiplication by \(P\), the positive remainder formula in [grouped_lobes.py](grouped_lobes.py) is nondecreasing in each of \(P,C,A\) and homogeneous of degree one. The unsmoothed cap and fixed-edge terms scale with \(P\), the integrated moving term with \(C\), and the low-frequency difference term with \(A\). Taking their minima, multiplying by positive factors and summing gives the claim. Freeze the physical bounds for all oscillatory parameters at the two ends of the outer interval. A prototype with data \((1,C_0,A_0)\) then pays any proposed lobe after multiplying by \(\max(P,C/C_0,A/A_0)\). The remaining normalization \(K e^{-l}\) can use the actual lower endpoint. This works even if the prototype is not itself the data of any single function. The [common price verifier](lobe_reference.py) uses the outer interval \([115.400,115.455]\).

With \(K-H=60\cdot10^9\), a linearly decreasing choice over 16 pairs of companion zeros gives a full upper bound below .999968391 on \([115.408,115.414]\). A different single test with \(K-H=100\cdot10^9\) gives **.9983129801304340 on the entire \([115.408,115.420]\)**. It uses ten cumulative height rows and the [fixed positive coefficients](companion_weights_100.txt) rounded to six decimal places. The primary, secondary and remaining lobe bounds are below .911351, .069141 and .000214 respectively; the unverified height charge is below .017604. The [linear program](companion_design.py) selects candidate coefficients. The executable below accepts the archived rational numbers directly.

~~~powershell
python -B round7/physical/lobe_reference.py --size 100000000000 --table round7/physical/companion_sieve_100.json
python -B round7/first_selected/companion_heights.py --size 100000000000 --panels 10 --table round7/first_selected/companion_rows_100.json
python -B round7/physical/companion_cover.py --lo 115.408 --hi 115.42 --size 100000000000 --count 1 --lobes 64 --mesh 80 --weights-file round7/physical/companion_weights_100.txt --sieve-table round7/physical/companion_sieve_100.json --height-table round7/first_selected/companion_rows_100.json --check
~~~

For signed displacements, clearing the distinct simple poles in the ratio gives a polynomial of degree exactly the number of displaced zero pairs, since its leading coefficient is the strictly positive limit at infinity. Disjoint sign-changing brackets enclosing that many positive roots in the squared coordinate exhaust its complex roots with multiplicities. The canonical-product lobe proof then applies. Beyond the last included zero at coordinate \(u_*\) the ratio is positive and at most
\[
 r+\sum_{e_j<0}|e_j|(b_j^2-a^2)/(u_*^2-b_j^2).
\]
Use this upper bound in the exterior tail, and absolute coefficient sums in the analytic remainder. The program checks each factor used for the remote zeros and accounts for the pole separately.

The cumulative table may additionally bound the positive part of the physical cosine throughout one frequency window, by a translated Green rectangle. Translating its angle by \(\pi\) bounds the negative part by the same number. Transfer signed cumulative prices only within that full window. For each spectral band compute upper envelopes for each sign of the *real* undamped transform. A monotone nonnegative transform uses the left height endpoint. Otherwise use 24 interpolation panels and the analytic second-derivative bound on every band. Make these envelopes decreasing by backward maxima, and sum their drops against the translated positive-cosine upper bounds. The absolute-value bound provides a second choice. In both computations the Lipschitz error of complex Gaussian convolution uses the full scalar count through the last height.

Each Selberg block offers a choice of positive, homogeneous linear forms in the lobe cap, variation and area. Choosing a valid branch independently at the prototype data and preserving that choice gives a positive linear upper bound at arbitrary physical lobe data. The optional three-integer table in [lobe_reference.py](lobe_reference.py) stores the aggregate outward-rounded coefficients in the prototype units. Tail minima are treated by the same fixed-branch rule. This gives a second transfer in addition to scaling by the largest component ratio.

The [rotated translated estimate](../first_selected/near_rotating.py) uses the two actual boundary integrals on the full translated axis. The tables store their halves. It divides the analytic cutoff by \(1+10^{-6}\) to charge the original boundary norms directly and checks that the resulting target multiplier is within \(2\cdot10^{-6}\) of one. The degree-nine detector pays nine eighths of the archived degree-eight horizontal allowance. Its first abscissa is .650, the minimum covered by that allowance. The positive-circle and signed-circle variants use the separate arguments in [ROTATING.md](../../round8/zero_strip/ROTATING.md) and [ROTATING_SIGNED.md](../../round8/zero_strip/ROTATING_SIGNED.md).
