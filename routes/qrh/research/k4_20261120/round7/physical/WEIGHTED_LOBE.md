# A Selberg square integrated directly against the first exterior lobe

Both first exterior lobes of the Logan test admit a direct upper bound with one fixed Selberg sieve level. The level may exceed the square root of their effective length. The moving endpoint then saves part of the Fourier remainder through integration by parts. The other positive exterior lobes and the entire analytic side retain the cited [physical cover](COVER.md) and [dilated sieve](DILATION.md).

On either side of the target write \(t(w)=\exp(c\pm(a+w)/K)\), \(0\le w\le b=2(\pi-a)\), and \(F(w)=g(a+w)\). Write \(F_0=\sin(a)/(2a)\), \(I=\pi\sin(a)/a\), \(A_1=\int_0^b F(w)\,dw\). By the monotonicity in the [edge proof](../../round2/local/EDGE.md), \(p(w)=-F'(w)/F_0\) is a probability density. A prime sum with weight \(F\) on this lobe equals \(F_0\) times the mean of its interval counts between \(t(0)\) and \(t(w)\). Point endpoints in the moving boundary have zero measure. The fixed endpoint lies strictly inside the target and has no prime under the contradiction hypothesis. The two orientations can therefore use the original half-open interval formulas. All endpoints and intervening locations lie between \(e^{l-r}\) and \(e^{c_++r}\) with \(r=10^{-6}\).

Fix \(z=C(e^l/K)^{1/2}\) on the *entire* physical slab, and take the Selberg coefficients from [the exact square identity](BILINEAR.md). Its main coefficient is at most \(1/G\), \(G=\log z+1.331\). The mean of the actual interval lengths is at most \(e^{c+r} A_1/(K F_0)\). This follows by integrating the monotone length once by parts and using \(|t'|\le e^{c+r}/K\). The prime weight, the Gaussian and the explicit-formula normalization give both first lobes together the upper cost
\[
 \frac{2(c_++r)e^{r/2}}I
       \left(\frac{e^r A_1}{G}+K e^{-l} F_0 z^2 E\right).             \tag{1}
\]
Here \(E\) is an upper bound for the mean Selberg remainder per \(z^2\), separately on each side. The common center in the main term cancels before taking endpoints. All other scalar costs are evaluated by the inherited verifier on the actual slab.

## A smoothed endpoint in each Fourier coefficient

The Möbius separation puts \(d=ghx,\ e=ghv\) and gives modulus \(m=gh^2xv\). In the dyadic block \(x\le D=z/(gh2^j),\ v\le P=z/(gh2^i)\) one has \(m\le m_* = z^2/(g2^{i+j})\). Write \(U_n\) for the previous normalized upper bound for this block at any allowed location, valid for every choice of separately bounded coefficients (or of corresponding second moments). It works for the signed Selberg coefficients and their absolute values.

At the fixed endpoint the bound is \(U_n\). At the moving endpoint the integrated bound is at most
\[
 U_n\min\left(1,\frac{m_* K e^{r-l}}{2\pi n F_0}
       \left(\frac13+b\left(\frac1{12}+\frac1{6K}\right)\right)\right).   \tag{2}
\]
Indeed integrate \(p(w)e^{2\pi i nt(w)/m}\) by parts, transferring the derivative to \(p(w)/t'(w)\) and retaining both boundary terms. The factor \(m/m_*=(x/D)(v/P)\) separates into two factors of modulus at most one. The same block sum bounds apply at both boundaries and at every intermediate location. The total variation plus the two endpoint moduli of \(p/t'\) are bounded by the factor \(K e^{r-l}(1/3+b(1/12+1/(6K)))/F_0\). To check the derivatives use the exact identity
\[
 g(u)=\frac1a\int_0^1\sin(a(1-v))\cos(uv)\,dv .
\]
Since \(0<a<\pi\), the inequality \(\sin(a(1-v))\le a(1-v)\) gives \(|g'|\le1/6,\ |g''|\le1/12\). Also \(|(1/t')'|\le |1/t'|/K\) on either orientation. These inequalities prove (2).

The original Vaaler main and Fejér majorant count both endpoints with equal coefficients. Each aggregated block bound is now multiplied by half the sum of 1 and the factor in (2). The zero-frequency Fejér majorant is charged in full. The tails after the truncation in \(g,h,i,j\) retain their unsmoothed bound for every frequency. All finite nonzero frequency coefficients of Vaaler and of the Fejér remainder are summed through the chosen order as in the [dilated sieve verifier](dilation.py).

## Optional small-frequency cancellation

For the signed Vaaler sawtooth terms the two endpoint sums occur **with opposite signs**. An additional bound applies when the normalized block estimates admit the separate coefficient multipliers \(D/x,P/v\). Denote by \(V_n\) the normalized upper bound with these multipliers, both lying between one and two, and by \(U_n\) the unweighted estimate. For the difference of the fixed and averaged moving sums divided by two the second bound is
\[
 V_n\,\pi n\,\frac{g2^{i+j}}{z^2}\,\frac{e^{c_++r} A_1}{K F_0}.          \tag{3}
\]
This follows by integrating the derivative of \(e^{2\pi i nt/m}\) from \(t(0)\) to \(t(w)\), because \(1/m=(g2^{i+j}/z^2)(D/x)(P/v)\). Taking the mean absolute ordinary length gives precisely the last factor. The implementation uses a 128-cell upper Darboux sum for the \(A_1\) occurring in (3). It takes the lesser of (3) and the symmetric two-endpoint estimate for each block and frequency group. Positive Fejér errors retain the prior unsigned endpoint cost. This option uses the [local coefficient energies](extras/weight_energy.py) and the bounds for their reciprocal-multiplied sequences. The option changes no estimate needed by the plain-supremum version.

## Comparing the same budget terms

The old budget charged the exact positive exterior area once at a common slope \(s_0\). Its first-lobe correction was an explicit sum over short cells of the decreasing values of \(F\), including the later local-sieve discounts. The verifier reconstructs precisely those two terms, \(2s_0 A_1\) and the old first-lobe correction. It subtracts (1) and clips the resulting gain below at zero before subtracting it from the complete unmodified budget. The area occurs with one common signed coefficient and is enclosed by the 8192-cell trapezoid rule with radius at most \(b^3/(144\cdot8192^2)\), since \(|F''|\le1/12\). This proves a direct cost comparison even when the separate charges are close. All numerical inequalities outside the positive binary64 kernel use 192-bit Arb. Its single extra per-term factor in (2) and the positive operations in (3) fit the same \(1+10^{-7}\) inflation, with fewer than \(2^{23}\) accumulated terms.

With only the original supremum coefficient bounds and the six rows **WEIGHTED** of the dilated verifier, the full cost is below .999892140 on the closed unrestricted slab \([115.1465,115.155]\). The next closed slab \([115.155,115.1604]\) uses QRH(7/8) and has cost below .999917519. Its high-ordinate charge is the same certified \(.005937108818\) transferred in [the covering proof](COVER.md).

~~~powershell
python -B round7/physical/weighted_lobe.py --lo 115.1465 --hi 115.155 --ratio 7 --order 8192 --complete --check
python -B round7/physical/weighted_lobe.py --lo 115.155 --hi 115.1604 --size 16000000000 --ratio 7 --order 8192 --complete --check
~~~


## The 64 secondary pairs

For \(j=1,\ldots,64\) retain the complete positive exterior lobe on \(u\in[v_j,v_j+b]\), \(v_j=2\pi j+a\), and its reflection. Put \(A=\sum_j\int_0^b g(v_j+w)\,dw\), \(P=\sum_j(1+\cos a)/(v_j^2-a^2)\). All these supports lie strictly within \(|u|<Kr\). The true summed peaks are at most \(P\). Let \(D_j=v_j^2-a^2,\ u_j=v_j+b,\ M_j=(1+\cos a)/D_j\), and
\[
 B_j=D_j^{-1}+4u_jD_j^{-2}+
       (1+\cos a)(2D_j^{-2}+8u_j^2D_j^{-3}),\qquad
 C=\sum_j\{\sin a(D_j^{-1}+(u_j^2-a^2)^{-1})+b B_j+2M_j/K\}.
\]
Direct differentiation gives \(|g''|\le B_j\) on this lobe and the displayed sine terms are the two endpoint derivative moduli. The peaks are unique by the previously proved log concavity. Thus the total variation of all lobes on one side is at most \(2P\).

Apply the Selberg square to each smooth lobe in the prime variable. Partial summation leaves the mean-density main term from its area and sawtooth errors integrated against the signed measure \(g'(u)\,du\). There are no exterior jump terms since both endpoints vanish. The Vaaler remainder uses the positive measure \(|g'(u)|\,du\). Both this density and the signed one have absolutely continuous representatives on each lobe, with the modulus of their derivatives at most \(|g''|\) almost everywhere. Integration by parts now gives the factor \(\min(1, m_* K e^{r-l} C/(4\pi n P))\) for the entire fixed-frequency error, after normalization by \(2P\). The lowest-frequency signed estimate follows instead by integrating \(g'\) against the exponential without absolute values, transferring its derivative to \(2\pi i n t'(w)/m\). This gives the factor in (3) with \(A_1/F_0\) replaced by \(A/P\). Formula (1) now holds with \(A,P\) in place of \(A_1,F_0\). The change from variation \(2P\) to \(P\) in (1) accounts for the original Vaaler coefficients in the code, which include both endpoints.

To deduct this new estimate from the old certificate it suffices to *lower* bound the numerical upper charge previously assigned to these same lobes. Each tested old tangent \(C_1(s,\eta)w+C_2(s,\eta)\), on \(0\le w\le b\), is at least \((C_1+C_2/b)w\). Evaluate this last coefficient with the largest old denominator addition among the six cells and the global addition. Both coefficients decrease with the addition as \(v>4\). Take the least over the reference scale 1.55 and all 39 tested scales \(s=ib/40\). Call it \(m_0\). At every level the old procedure discounted no more than the improvement guaranteed by the chosen tangent on the whole width enclosure; taking the maximum of such reductions still leaves at least \(m_0 w\). Any excess charged in the old peak bound is nonnegative. Its previous integrated charge on the 64 pairs was consequently at least \(2m_0 A\). The new deduction takes the positive part of this lower bound minus the new upper charge. The exact area difference uses one common area enclosure. A 1024-panel trapezoid integrates each smooth lobe with radius \(b^3 B_j/(12\cdot1024^2)\). The [secondary calculation](secondary_lobes.py) leaves all further exterior lobes, the nonlocal Gaussian tail and the analytic terms in the budget.

## Averaging the endpoint inside the target

For any \(0<\epsilon<a\), allow the formerly fixed endpoint to move from \(t(0)\) inwards to \(\exp(c\pm(a-\alpha)/K)\), with \(0\le\alpha\le\epsilon\) uniformly distributed, independently of \(w\). Every added point lies strictly inside the supposed prime-free target. The prime sum on the original exterior lobe is therefore preserved. The increase in the upper mean length is at most \(e^{c+r}\epsilon/(2K)\), so use \(A_1+F_0\epsilon/2\) in the main term of (1) and in the length factor of (3). The other moving endpoint retains the original derivation. Integrating the new uniform-density endpoint by parts exactly as in (2) gives it a factor at most
\[
 \min\!\left(1,\frac{m_* K e^{r-l}(2+\epsilon/K)}
                         {2\pi n\epsilon}\right).
\]
Both frequency signs and the half-open endpoint convention are covered as above. The flag **--inside-width** is optional and defaults to zero.


## Infinite Fourier expansion after both endpoints are smoothed

With a positive internal averaging width, or on a secondary lobe, the sawtooth series can replace its finite Vaaler approximation. For each fixed integer modulus \(m\) the set of \(w\) at which a moving endpoint is an exact multiple of \(m\) has measure zero. The Fejér means of the sawtooth converge almost everywhere to the fractional part minus \(1/2\), and are bounded by its essential supremum. Dominated convergence first handles each endpoint and each of the finitely many sieve coefficients. For secondary lobes use the signed measure \(g'(u)\,du\). The constant term cancels on both constructions.

The resulting normalized nonzero coefficient at \(n\ge1\), accounting for both Fourier signs, is \(2/(\pi n)\) times the block bound for the half-difference of endpoints (or the derivative measure divided by \(2P\)). Let \(B_\infty\) be the same averaged by-parts factor as above with \(m_*=z^2\) and the factor \(1/n\) removed. On the first lobe it is half the sum of the moving and internally averaged endpoint constants; on the secondary lobes it is \(K e^{r-l}z^2 C/(4\pi P)\). Absolute convergence follows since the normalized signed sum at each frequency is bounded by
\[
           \left(\frac{K_0}{G}\right)^2\min(1,B_\infty/n),
       \qquad K_0\ge (G_{\rm exact}/z)\sum_{d\le z}|\lambda_d|.
\]
Here \(G_{\rm exact}\ge G\) and \(K_0\) is the sieve-weight first-moment bound. For \(n>N\) the whole Fourier tail thus costs at most \(2(K_0/G)^2 B_\infty/(\pi N)\), without any truncation of \(d,e\). For \(n\le N\), group the positive frequencies \([u,v]\) and use the exact coefficient sum \(2(\psi(v+1)-\psi(u))/\pi\), with \(\psi\) the logarithmic derivative of the gamma function. The signed small-frequency estimate and the two differentiated endpoint bounds remain available in every block. The omitted \(g,h\) and dyadic blocks of the finite Möbius separation retain their old absolute bounds times \(\min(1,B_\infty/u)\), since the artificial modulus after inversion still satisfies \(gh^2 xv\le z^2/g\le z^2\). The computations use \(g,h\le 2^{40}\), 44 dyadic blocks, and \(N=2^{48}\). The sieve summation has 4,444,110 positive grouped terms per frequency band, and the binary64 loop uses no large-frequency powers exceeding the normal binary64 range. There is no zero-frequency Fejér cost in this calculation. The script falls back to the finite approximation when the infinite expansion is not requested.


## Closed coverage from the integrated sieve

With the unweighted and reciprocal-multiplied Selberg coefficient norm inputs from **extras/weight_energy.py**, the following full upper costs cover the listed closed slabs. The first unrestricted row connects with the six weighted Vaaler rows in [the dilated cover](dilated_cover.py). No assumption on zeros above the published verified height is used on unrestricted rows. The QRH row uses the same QRH(7/8) and finite high-zero reference as in [the preceding cover](COVER.md). The verified interval at every real \(x\) is \((x,x+4x^{3/4})\).

| Closed \(\log x\) interval | Hypothesis beyond the verified height | Complete cost below |
|---|---|---:|
| \([115.1465,115.155]\) | unrestricted | .999892140 |
| \([115.155,115.24]\) | unrestricted | .996178162 |
| \([115.24,115.279]\) | unrestricted | .996440 |
| \([115.273,115.285]\) | unrestricted | .998088 |
| \([115.275,115.290]\) | QRH(7/8) | .998476 |

Run from the directory containing the round folders, with the upstream six-row sieve table and 96-panel high-zero reference verified separately by their cited programs. The three Poisson runs have the same frequency cutoff \(2^{48}\).

~~~powershell
python -B round7/physical/weighted_lobe.py --lo 115.1465 --hi 115.155 --ratio 7 --order 8192 --complete --check
python -B round7/physical/weighted_lobe.py --lo 115.155 --hi 115.24 --ratio 36 --order 32768 --energy --complete --check
python -B round7/physical/weighted_lobe.py --lo 115.24 --hi 115.279 --ratio 74 --order 281474976710656 --energy --secondary --secondary-ratio 90 --inside-width .00015 --poisson --complete --check
python -B round7/physical/weighted_lobe.py --lo 115.273 --hi 115.285 --ratio 72 --order 281474976710656 --energy --secondary --secondary-ratio 90 --inside-width .0001 --poisson --complete --check
python -B round7/physical/weighted_lobe.py --lo 115.275 --hi 115.290 --size 16000000000 --ratio 72 --order 281474976710656 --energy --secondary --secondary-ratio 90 --inside-width .0001 --poisson --complete --check
~~~


## A pointwise transfer of the finite high-ordinate charge

Keep \(S=16000000000\) and \(K=H+S\) fixed, and denote the reference quantities on \([l_0,h_0]=[115.040500,115.041000]\) by a subscript zero. Take \(l\ge l_0,h\ge h_0\), so \(a\le a_0\), and let \(v=a_0S/K\in(0,\pi/2)\). In every cell of the reference height partition write \(x=[1-(H+d_i)/K]_+\), so \(0\le a_0x\le v\). The script verifies that \(\sin(v)+2Qa_0/(\sqrt\pi K)<1\); consequently neither outer cap at one is active. The new sinusoidal numerator bounded by \(ax\), and the old one bounded below by \(a_0x\operatorname{sinc}(v)\), show that the whole new numerator including the \(2Qa/(\sqrt\pi K)\) term is at most \((a/a_0)/\operatorname{sinc}(v)\) times the old one. Here \(\operatorname{sinc}(v)=\sin(v)/v\). The sine denominators give another factor \(\sin(a_0)/\sin(a)\). For every actual zero, QRH(7/8) gives \(e^{(\beta-1)(l-l_0)}\le e^{-(l-l_0)/8}\). Comparing the *step functions* before integrating them against the counting measure allows all three factors to be multiplied; the [old certified finite cost](../first_selected/LOW_CONTINUATION.md) may be multiplied by their product or by 1, whichever is smaller. The remote Gaussian cost has already been reevaluated on the actual slab. The option **--transfer** takes this additional reduction.

The following three closed intervals extend the table. The first has unrestricted zeros and the last two use QRH(7/8). Their normalized upper costs respectively lie below **.999741**, **.999348**, and **.999597**. Thus the unconditional finite-RH input reaches \(115.290\), and the QRH input reaches \(115.296\), subject to the common local Selberg norm inputs.

~~~powershell
python -B round7/physical/weighted_lobe.py --lo 115.282 --hi 115.290 --ratio 72 --order 281474976710656 --energy --secondary --secondary-ratio 90 --inside-width .0001 --poisson --complete --check
python -B round7/physical/weighted_lobe.py --lo 115.287 --hi 115.295 --size 16000000000 --ratio 72 --order 281474976710656 --energy --secondary --secondary-ratio 90 --inside-width .0001 --poisson --transfer --complete --check
python -B round7/physical/weighted_lobe.py --lo 115.294 --hi 115.296 --size 16000000000 --ratio 72 --order 281474976710656 --energy --secondary --secondary-ratio 90 --inside-width .0001 --poisson --transfer --complete --check
~~~


The two required row envelopes and the first moment in the Poisson calculation are proved in [Squared Selberg weights](extras/WEIGHT_ENERGY.md). Those coefficient identities and the separated sampling lemma hold at all positive dimensions and frequencies. The present enlarged finite ranges have their own numerics. Throughout the replay rows \(2^{60}<z<2^{72}\), \(2^{165}<t<2^{168}\), \(1\le g,h\le2^{40}\), \(0\le i,j\le43\), and \(1\le n\le2^{48}\). Hence \(2^{-63}<D,F<2^{72}\), \(2^{-224}<K_{\rm inv}<1\) where \(K_{\rm inv}=z^2/(ntg2^{i+j})\), and \(K_{\rm top}<2^{222}\). The positive expanded term \(32ntg^3h^2 2^{2(i+j)}/z^4\) is below \(2^{354}\). The reciprocal denominator, powers of block dimensions and product of bounded row weights consequently stay in the normal binary64 range. A nonzero energy row has a main contribution from the units modulo 210 and \(G_{k_0}(1)=1\); the trivial envelope uses a coefficient bound at least \(1/G\), so a nonzero row envelope exceeds \(10^{-6}\) throughout these finite boxes. Exact zero rows enter as zeros. The group counts, integer frequency endpoints and powers of two are exactly representable, and \(1+10^{-7}\) dominates both per-term rounding and the accumulation of 4,444,110 positive terms. The trigonometric calculations, summed harmonic coefficients and final tail are performed in Arb.
