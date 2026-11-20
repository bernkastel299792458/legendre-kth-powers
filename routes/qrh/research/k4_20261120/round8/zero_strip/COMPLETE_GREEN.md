# Cumulative physical phase weights at all finite heights

Use the [two-source Green estimate](WEIGHTED_GREEN.md), the [compact spatial density](../../round7/spatial/PROFILE.md), and its [two directed Fourier envelopes](../../round7/spatial/signed_profile.py). The following pointwise comparisons allow each cumulative-height decrement of the actual explicit formula to use the physical phase. Every detector pair uses a single mollifier and one radial determinant on its two abscissae. Different pairs can choose different determinants.

For a physical cell \([L_0,L_1]\) put \(\omega=L+\log(1+4e^{-L/4})/2\), \(L_0\le L\le L_1\). The implementation encloses this entire range before evaluating any cosine weights. Its physical chord and its ratio of coefficients at two real-part nodes are frozen at \(L_0\); this upper-bounds the real exponential throughout the cell because \(\beta<1\). Let \(B=(\beta-a)_++C(\beta-b)_+\) and \(V=\epsilon K(\beta)\) as in the preceding proof. The cosine frequency in this construction may be \(\omega\) or \(2\omega\). For each fixed \(L\), choose \(\epsilon=C\exp[-m\omega(b-a)]\), \(m=1,2\), with \(C\) fixed. Verify positivity over the whole cell. At any sampled height \(T_j\) the new source integral uses the frozen mollifier at \(T_j+.1\). Each underlying normalized endpoint norm therefore covers the full interval \([U,\log(e^V+.1)]\) whenever \(U\le\log T_j\le V\); if necessary split this interval to preserve the half-unit restriction of the source norm. The new angular bound uses the widened upper edge as well. The older scalar curve still uses the original \(T_j\). Both curves are valid and can be compared.

For \(\Theta\ge\beta>a\), write \(v(\beta)=V/B\), with bounds
\[
 v_{\rm lo}=\min\{\epsilon,V(\Theta)/B(\Theta)\},\qquad
 v_{\rm hi}=\epsilon\sinh(m\omega(b-a))/(m\omega(b-a)).
\]
The quotient increases on \((a,b]\) and decreases on \([b,\Theta]\). With frequency \(\omega\), to charge all positive cosine parts use \(1/(1+v_{\rm lo})\) times the positive Green weight. The same bound applies to negative parts upon reversing the signs of both source cosines.

With frequency \(2\omega\), write \(u=|\cos(\omega\gamma)|\). The ratio of the absolute cosine reward to the Green weight is
\[
 \frac{u}{1-v+2vu^2},\qquad 0\le u\le1.
\]
Its maximum is \(1/(1+v)\) for \(v\le1/3\), and \(1/\sqrt{8v(1-v)}\) otherwise. For a \(v\)-interval check its endpoints, since the denominator is affine in \(v\) for fixed \(u\). Thus an upper bound for the ratio is the maximum of \(1/(1+v_{\rm lo})\) and the second expression at \(v_{\rm hi}\) if \(v_{\rm hi}>1/3\). This gives an all-height estimate independent of the signs of the actual centered Fourier transform.

A set of pairs can also be charged together. Multiply each pair's nonnegative Green weight by its positive physical chord coefficient, then add the \(B\) terms and the \(V\) terms separately. Between real breakpoints \(B_\Sigma\) is affine and \(V_\Sigma''=(m\omega)^2V_\Sigma\). Thus its hyperbolic sine interpolation on a cell of length \(q\) is exact. Relative to the linear interpolation of the endpoint values of \(V_\Sigma\), it lies between \(m\omega q/\sinh(m\omega q)\) and one, since \(x\le\sinh x\) and \(\sinh(x)/x\) increases. The quotient \(V_\Sigma/B_\Sigma\) on the cell is consequently bounded by its smaller endpoint ratio times this lower factor, and by its larger endpoint ratio above. If the first left endpoint has both values zero, use its right endpoint ratio in this argument. After the final breakpoint \(V_\Sigma\) decreases and \(B_\Sigma\) increases. The individual-pair ratio formula therefore works with these certified joint extrema. Since every pair's own test is nonnegative on all determinant zeros, different pairs may choose different determinants before summation.

## The Abel sum

Let \(E(y)\) be the original decreasing majorant, including its tail, and \(T_0<T_1<\cdots<T_M\) the original height samples with \(E(d T_0)=1\). As in the spatial certificate, freeze the frequency scaling here at \(d_{\min}=\log(1+4e^{-L_1/4})\). For each decrement \(E(d_{\min}T_{j-1})-E(d_{\min}T_j)\), the associated measure is the **entire cumulative** population \(H<\gamma\le T_j\). If \(d_{\max} T_j\) is within the proven positive interval of the centered transform, use its positive cosine parts; elsewhere use absolute cosine parts. This is valid simultaneously: for an individual root in the positive interval every applicable positive-part term uses the same cosine, and all remaining absolute-value terms are at least the positive part. A root outside the positive interval appears only in absolute-value terms. For a spatial test of known nonnegative transform the first comparison is valid everywhere.

The finite-height removal of the damping factor costs at most \(2d_{\max}\sum_{H<\gamma\le T_M} e^{(\beta-1)L_0}\). This sum is bounded by the final cumulative ordinary real-part chords and total count. For the residual frequency tail, retain the original full amplitude and all its ordinary costs; the normalized error \(d_{\max}\) is never summed over the infinite tail. The explicit prime-power cost scales by the ratio of the spatial density's upper peak to \(4/3\), and the verified critical-line and trivial-zero contributions are kept.

The optional sign-separated replay uses decreasing \(E_+,E_-\) for the positive and negative centered transform. Intersect each with the original envelope. On a height decrement put \(D=\max(\Delta E_+,\Delta E_-)\) and \(\alpha=\min(\Delta E_+,\Delta E_-)/D\) when \(D>0\). After possibly changing the cosine's sign, the reward divided by \(D\) is \(z_++\alpha(-z)_+\), \(z=\cos(\omega\gamma)\). The first-frequency ratio is bounded by
\[
 \max\{1/(1+v_{\rm lo}),\,\alpha/(1-v_{\rm hi})\};
\]
this follows by monotonicity on each of \([-1,0]\) and \([0,1]\). The absolute-cosine second-frequency bound is also available. The final unsigned tail covers both remaining directed envelopes since \(z_++(-z)_+\le1\). Compare the two *complete* Abel sums after integration. The program takes the minimum only within one common decomposition or between complete results.

For each fixed pair group the underlying ordinary hinge upper bounds may use the previous convex envelopes in the real part and later cumulative height. The Green bound for that group is computed separately from its own two exact source lines. Replacing the old cost of that group's chord coefficients by the lesser legal upper bound, with the unpaired positive coefficients left in full, preserves the estimate on the complete population. Alternative overlapping groups can compete by a maximum of their individual savings; their savings are not added.

The executable [complete_green.py](complete_green.py) evaluates both the full scalar physical upper expression and its phase-weighted counterpart. Its API accepts a proved spatial envelope, the associated density height and a flag for a globally nonnegative centered transform. For the original spatial polygon the default density height is \(3/2\).

For a fixed pair partition first maximize each single-pair saving over admissible harmonics. A group offers the improvement of its total legal saving over the sum of those single-pair savings on its own keys. The interval scheduling step selects disjoint groups and retains every individual saving outside them. Physical coefficients are never reused. Different pair partitions compete by their maximum and their results are not added. The optional adaptive coefficient is the minimum of the physical ratio and \(.97(2x)/(1-e^{-2x})\), where \(x=(b-a)\inf m\omega\). Its positivity follows because \((1-e^{-2v})/(2v)\) is decreasing for \(v>0\). The source Poisson multipliers can be evaluated with unit cosine amplitude at both lines, since the exact multiplier is increasing in that amplitude.

## Closed bridge and source tables

The [signed rotated scalar tests](ROTATING_SIGNED.md) join the [positive rotated scalar tests](ROTATING.md) at \(135\), then the [multiple-harmonic Green tests](COUPLED.md) at \(137.25\). The latter connect to the [multi-source Green tests](MULTI_RAW.md) at \(139.25\), then the [two-source positive and absolute formulas](RAW_GREEN.md) and the component bridges below. Together these particular certificates give the half-line \(L\ge128\).

The seven-mollifier moving-line table and the two-frequency certificate cover **the complete physical interval \([142.9,143.44]\)**. At height \(T_j\), the scalar calculation selects among the usual critical-line result and the shift \(h=.008\), hence \(\ell=.492\), at each abscissa. Each signed two-source Green calculation keeps one taper and one radial determinant but may independently use either of these auxiliary interpolation lines at its two sources. The source is [shift_rows_16.json](../critical/shift_rows_16.json), produced by [shift_parallel.py](../critical/shift_parallel.py), with its seven original triples, 16 time slabs per unit log-height, right cutoff 320, and outward rounding by \(10^{-20}\). The calculation used 6 ordinate samples per such slab, \(\log T_{\max}=41\), and the real-part grid \(.65,.652,\ldots,.874,.875\). It split the physical interval into 27 closed cells of width .02. The largest reported total enclosure was \(0.997\pm0.000289<0.9973\). This connects to the separately proved upper half-line at \(143.434\). From this directory run

~~~powershell
python -Bu complete_green.py --first 142.9 --last 143.44 --pieces 27 --uniform 6 --nh 6 --sub 16 --hi 41 --step 4 --shift-rows ../critical/shift_rows_16.json --shifts '.008' --menus '2:0,3:0,4:4,5:5,6:6'
~~~

This uses the original centered spatial polygon, the analytic first-lobe positivity radius, and the unsigned inverse-square infinite tail. Neither a directed two-envelope decomposition nor any unverified zero-count assumption is used in this bridge.

Using all three optional left lines from that same archived source table extends the continuous bound to **\(L\ge142.43\)**. The first command below covers \([142.43,142.7]\), with its largest total enclosed by \(0.999\pm0.000559<0.99956\). The second covers \([142.7,142.9]\), with its largest total enclosed by \(0.992\pm0.000451<0.99246\).

~~~powershell
python -Bu complete_green.py --first 142.43 --last 142.7 --pieces 15 --uniform 3 --nh 8 --sub 16 --hi 41 --step 4 --shift-rows ../critical/shift_rows_16.json --menus '2:0,3:0,4:0,4:4,5:0,5:5,6:0,6:6,7:0,8:0'
python -Bu complete_green.py --first 142.7 --last 142.9 --pieces 10 --uniform 2 --nh 8 --sub 16 --hi 41 --step 4 --shift-rows ../critical/shift_rows_16.json --menus '2:0,3:0,4:0,4:4,5:0,5:5,6:0,6:6,7:0,8:0'
~~~

The original centered spatial polygon and three original \(Q=2310\) mollifiers give a complete upper bound below \(.9986\) on \([143.7,143.875]\). The seven physical subintervals of width \(.025\) include their endpoints. This certifies the fourth-power intervals in this range under QRH(7/8) and the project's verified-height inputs. It joins the pre-existing far-end estimate. The frozen endpoint table [phase_norms.json](phase_norms.json) contains integer ceilings of the two norms and the edge in units of \(10^{-20}\). From this directory a small replay is

~~~powershell
python -Bu complete_green.py --first 143.7 --last 143.875 --pieces 7 --nh 48 --sub 4 --hi 41 --step 4 --cells 96 --load-rows phase_norms.json
~~~

The table can be regenerated without relying on its contents. The following command recomputes every source norm, including its upper halo, from the full Euler mollifier and the [certified fourth-moment table](../critical/frozen_sweep.py). It additionally proves the indicated closed physical cell.

~~~powershell
python -Bu complete_green.py --first 143.85 --last 143.875 --nh 16 --sub 4 --hi 41 --step 4 --cells 96 --save-rows replacement.json
~~~

For a [moving left boundary](../critical/MOVING_LINE.md) the same strip proof uses the actual \(\ell=1/2-h\) in both harmonic kernels and \(\theta=(r-s)/(r-\ell)\). The auxiliary pole remover is \((z-1)/(z+2h)\), as in the displaced-moment proof, with the same lower transfer factor at the hinge. The determinant, the tapered residual and its zeros are unchanged by this auxiliary interpolation choice. Each of the two source integrals for one fixed mollifier and radial polynomial may independently select its best proved \(h\). The two Poisson attenuation ratios decrease with frequency, by monotonicity of \(x\coth x\), so they may be evaluated conservatively at 140 throughout these physical cells.

The [moving-row adapter](frozen_green.py) uses an exported source table only in its certified region. The scalar height \(T_j\) can use a slab including either endpoint. The Green freeze is \(T_j+.1\), and the adapter explicitly selects the slab containing \(\log(T_j+.1)\). If that slab is unavailable the cumulative height retains its entire scalar cost. The [compact displaced table](phase_shift_norms.json) can be rebuilt with `python -Bu phase_shift_table.py` from three original moment rows and the independent displaced-moment routine. The larger [seven-mollifier export](../critical/shift_rows_16.json) comes directly from [the displaced scalar calculator](../critical/shift_parallel.py).

Several adjacent physical cells can share a single angular estimate. For a common window \([L_-,L_+]\) enclose the physical frequency over the entire window, and allocate the paired hinge coefficients at \(L_+\). The jump of the divided-difference slopes at \(s_j\) is the integral of \(L^2e^{(s-1)L}\) against the nonnegative linear hat supported on \([s_{j-1},s_{j+1}]\), with unit value at \(s_j\). This follows by integrating twice by parts and applies also to unequal adjacent spacings. The logarithmic derivative of the integrand is \(s-1+2/L\), and \(s_{j+1}-1+2/L_-<0\) is checked. Hence every scalar cell at a smaller or equal left endpoint has at least the allocated physical coefficients available. Its remaining coefficients stay at full price. Each physical subcell still computes its own height-envelope decrements, scalar integral and damping charge. The option `--uniform 6` shares the angular certificate across at most six adjacent subcells.

## Fractional allocation across detectors

The optional [allocation verifier](phase_packing.py) can add savings from overlapping source groups that use different mollifiers and radial determinants. Normalize the available physical hinge coefficient at each abscissa to one. An ordinary two-source saving consumes one unit at its first knot \(i\) and \(Cw_i/w_j\) at its second knot \(j\). A group consumes the corresponding amounts at each of its distinct paired indices. If certified saving \(s_g\) has these consumptions \(u_{jg}\), any \(x_g\ge0\) with \(\sum_g x_g u_{jg}\le1\) simultaneously proves a saving of \(\sum_g x_g s_g\). This is just the sum of the individual pointwise majorants, with every unused ordinary hinge left unchanged.

For \(D=10^6\) the program first replaces each consumption by the larger integer ceiling \(\lceil D u_{jg}\rceil/D\). It tests a greedy order or obtains a proposal from `scipy.optimize.linprog`, then rounds the proposed coefficients down to integer multiples of \(1/D\). Each new coefficient \(n_g/D\) is capped separately by every remaining integer resource. The verifier subtracts \(\lceil n_g\lceil Du_{jg}\rceil/D\rceil\) resource units and checks that every final resource is nonnegative. Thus all analytic costs and gains are certified with Arb and feasibility is checked with integers independently of the numerical optimizer. The mode is inactive in the original 27-cell calculation above.

Additional displaced left rows are regenerated by `python -Bu phase_shift_extra.py`, using the already certified `uniform_fourth` on each archived slab. This invokes the same [displaced mean verifier](../critical/shift_detector.py) at \(h=.016,.020,.026\), using its original adaptive short core. The result is [phase_shift_extra.json](phase_shift_extra.json). It extends the existing endpoint table while retaining its original right and angular bounds.

With four of the available displacements and the integer resource verifier, nine closed cells cover \([142.25,142.43]\). The largest total was enclosed by \(0.9997\pm0.0000806<0.999781\). The first cell alone has ordinary cost above \(1.02543\). Combined with the preceding bridges this covers the complete conditional half-line \(L\ge142.25\). The one-line replay is

~~~powershell
python -Bu complete_green.py --first 142.25 --last 142.43 --pieces 9 --uniform 3 --nh 8 --sub 16 --hi 41 --step 4 --shift-rows phase_shift_extra.json --shifts '.008,.012,.016,.020' --menus '1:0,1:1,2:0,2:2,3:0,3:3,4:0,4:4,5:0,5:5,6:0,6:6,7:0,7:7,8:0,8:8' --pack linear
~~~

A further option `--pack cone` lets a positive combination of proved tests majorize the physical hinge profile in the real part. It suffices to compare piecewise linear functions at their breakpoints, including \(7/8\). In computing the price of any recorded gain, multiply the upper ceilings of its hinge consumptions by the ordinary hinge prices and subtract the proved saving. For its guaranteed coverage use one less integer unit at every knot. These two roundings are in opposite directions. Given arbitrary nonnegative proposed combination coefficients, the verifier rescales all of them by at least the maximum of the target-to-achieved ratios at the nonzero grid vertices. The two profiles vanish to the left of the first included knot, so the rescaling proves domination on the whole QRH range. Ordinary individual hinges may be part of the combination, and the lower real-part terms retain their previous full price.

On the uniform real-part grid the optional [many-source adapter](angular_packing.py) supplies three residue classes of fourteen source nodes spaced by .003. For each class it calls the [independent angular certificate](../../round7/spatial/angular_certificate.py) using modes 1, 2, 3 for a positive cosine and 2, 4 for an absolute cosine. The weights in that certificate have exactly the physical ratio \(\exp(.003L)\). Each radial determinant and mollifier is kept fixed along the fourteen nodes. Each node may independently choose its auxiliary left boundary as above. At every relevant line the verified strip Poisson multipliers at frequency 140 are below \(10^{-7}\), hence so are the multipliers at every required harmonic. For a source with angular mean \(kw_i\) and coefficients \(c_{im}\), its weighted integral is thus at most \(kw_i+10^{-7}\sum_m|c_{im}|\) times the ordinary moment. The adapter keeps the full certified edge and all radial factors. It passes the resulting cost into the same allocation check as the independently proved two-source tests.

2026-11-20. Joint project attribution to Claude and Codex.
