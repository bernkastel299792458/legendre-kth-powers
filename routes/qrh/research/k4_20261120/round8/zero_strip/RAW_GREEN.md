# Joint pointwise use of different positive Green tests

Assume QRH(7/8) and the source moment and verified-height certificates of the [complete bridge](COMPLETE_GREEN.md). This refinement combines different determinants before comparing their joint zero weight with the physical cosine. Every individual test is the globally nonnegative two-source [Green weight](WEIGHTED_GREEN.md). It therefore charges the target zeta zeros even when the auxiliary determinants have different additional zeros.

Write \(H_j(\beta)=(\beta-s_j)_+\) for the ordinary hinges at the real-part knots, with frozen physical coefficients \(w_j>0\). The portion to majorize is \(R(\beta)=\sum_{j\ge j_0} w_jH_j(\beta)\), where \(s_{j_0}\ge.795\). Earlier terms keep their full scalar cost. Any nonnegative multiple of an ordinary hinge can be purchased at the known scalar cost irrespective of the physical angle. A previously certified projected group can be purchased as a lower profile \(G(\beta)z\), where \(G\) is a nonnegative sum of hinges and \(z\) denotes the required positive cosine part or absolute cosine. Its availability follows from its own pointwise majorant and its own source estimate. It consumes no old scalar cost until the complete new estimate succeeds.

For any source pair \(a,b\) in the grid, independently choose one taper and one radial polynomial for its two sources. Its raw physical weight is \(w_a[B(\beta)+V(\beta)\cos(\nu\gamma)]\), with \(B=(\beta-a)_++C(\beta-b)_+\) and \(V=\epsilon K\) from the two-source formula. For a cell in \(L\) let \(x=(b-a)\inf\nu\), and take \(C=t\,2x/(1-e^{-2x})\) with \(t=.52\) or \(.97\), and \(\epsilon=C e^{-(b-a)\nu}\). The global positivity condition holds since \((1-e^{-2u})/(2u)\) decreases on \(u>0\). All positive multiples of the resulting tests are available. Their retained source and angular costs are the complete, unscaled two-source costs. The second source can be at the terminal real part \(7/8\); its source cost is still charged in full.

## Lower profiles between real-part knots

On every open grid cell \(B\) is affine and \(V''=\nu^2V\), with \(V\ge0\). Let \(\mathcal I\) denote linear interpolation between that cell's endpoints. If \(g\) is an upper bound on all cell widths, then

\[
 \frac{\nu g}{\sinh(\nu g)}\,\mathcal I V\le V\le\mathcal I V.
\]

The upper bound is convexity. The lower bound follows by writing the exact two-point solution using hyperbolic sines and using \(u\le\sinh u\) on both interpolation numerators. It remains valid on the last shorter grid cell. Write \(\alpha=\nu g/\sinh(\nu g)\).

For positive physical frequencies put \(z=\cos(\omega\gamma)\) and use \(\nu=\omega\). For \(0\le z\le1\), every raw summand satisfies \(B+Vz\ge z(B+V)\). For \(z<0\) each raw test is nonnegative and the requested reward is zero. Thus it suffices for the appropriate sums of ordinary hinges, projected groups and raw columns \(w_a(B+\alpha V)\) to dominate \(R\) at every real-part knot. The lower interpolation formula proves the required comparison at all intermediate real parts. It is valid for the entire physical cell because the frequency balls enclose every actual frequency.

For an arbitrary spatial sign put \(z=|\cos(\omega\gamma)|\) and use \(\nu=2\omega\). The raw column is \(w_a[B+V(2z^2-1)]\). Sum the chosen ordinary constant-angle hinges and the \(w_a B\) into \(b\), the positive amplitudes into \(v\), and the previously projected linear profiles into \(G\). At each knot a lower bound is \(b+v'(2z^2-1)+Gz\), with \(v'=v\) for \(0\le z\le1/\sqrt2\) and \(v'=\alpha v\) for \(1/\sqrt2\le z\le1\). These are the two opposite signs required by the upper and lower real-part interpolants. Thus one needs the two minima of

\[
 (b-v')/z+2v'z+G
\]

on the respective angular intervals. For \(v'>0\) and \(b-v'>0\) the minimum occurs at \(\sqrt{(b-v')/(2v')}\) clipped to the endpoints. With \(v'=0\) use the right endpoint. At \(z=0\) nonnegativity is already guaranteed. The code discards proposals when a positive denominator cannot be certified. The two verified minima and linear interpolation prove the bound simultaneously for all angles and all real parts.

## Finite certificate

The [verifier](raw_cone.py) uses a floating linear program solely to propose nonnegative coefficients. It reconstructs their exact binary values as Arb numbers, recomputes every selected source price and uses one common radial polynomial inside each pair. It sums the resulting profiles at every vertex. It then multiplies both the candidate and its cost by at least the largest target-to-achieved ratio. The achieved denominator is the first-harmonic nodal profile or the analytically minimized second-harmonic profile above. This certification step is independent of feasibility or optimality claims from the linear solver. The output competes with all previous complete scalar and projected bounds at the same cumulative height. The complete finite Abel sum, the infinite inverse-square tail, damping and prime-power terms use the preceding physical certificate.

With only the first raw harmonic the full cell \([141.2,141.21]\) has scalar cost \(1.058722372704\) and signed cost \(0.9867\pm0.0000488\). This reported cell calculation uses `.012,.016` as the available displaced lines, in addition to the ordinary critical line. Reproduce it with

~~~powershell
python -Bu complete_green.py --first 141.2 --last 141.21 --nh 4 --sub 16 --hi 41 --step 4 --shift-rows phase_shift_extra.json --shifts '.012,.016' --menus '3:0,4:4,5:0' --raw-cone
~~~

The complete contiguous bridge \([140.95,142.25]\) used 52 closed physical cells of width .025. Its maximum complete upper bound was enclosed by \(0.996\pm0.000784<0.9968\). The ordinary scalar bound on the first cell was \(1.067190489630\). Together with the [previous closed bridges](COMPLETE_GREEN.md), this establishes the conditional fourth-power assertion throughout \(L\ge140.95\). The 227358-byte displaced source file has SHA-256 `FDA6719C59EFA3AA087E774578D5197F5ECA8E4C70CAE9855DF72F50037E8CDA`. The replay is

~~~powershell
python -Bu complete_green.py --first 140.95 --last 142.25 --pieces 52 --uniform 5 --nh 6 --sub 16 --hi 41 --step 4 --shift-rows phase_shift_extra.json --shifts '.012,.016' --menus '3:0,4:4,5:0' --raw-cone
~~~

The second raw harmonic covers the remaining spatial signs. With both raw modes enabled fifteen more closed cells cover \([140.65,140.95]\), with maximum enclosure \(0.997\pm0.000843<0.99785\). This joins the conditional upper half-line at \(140.95\).

~~~powershell
python -Bu complete_green.py --first 140.65 --last 140.95 --pieces 15 --uniform 3 --nh 6 --sub 16 --hi 41 --step 4 --shift-rows phase_shift_extra.json --shifts '.012,.016' --menus '3:0,4:4,5:0' --raw-cone --raw-abs
~~~

For stable enclosures on a common physical window, write \(u=\min((\beta-a)_+,b-a)\), \(v=(\beta-b)_+\), \(h=b-a\). The amplitude equals \(C\int_{h+v-u}^{h+v+u}e^{-\nu t}\,dt/2\). Both integration endpoints are nonnegative, so the amplitude decreases with \(\nu\), and its entire range follows from the two frequency endpoints. The edge majorant \(1+C+(C/2)(1+e^{-2\nu h})\) decreases as well.

2026-11-20. Joint project attribution to Claude and Codex.
