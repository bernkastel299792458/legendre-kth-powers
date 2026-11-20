# A tighter Mellin integral for the original sieve

Keep the mollifier, its line means, the angular edges, and the height and physical partitions of [the exact bridge](../../round6/reduction/EXACT_BRIDGE.md). For \(z=e/2+it\), \(Q=2310\) and \(\zeta_Q(s)=\zeta(s)\prod_{p\mid Q}(1-p^{-s})\), the continuous part of the right mean is controlled by
\[
I_e=\frac1\pi\int_0^\infty\left|\frac{A(Wz)}{z\zeta_Q(1+z)}\right|^2dt,\qquad
A(w)=\int_0^1 e^{-wv}\,dv .
\]
The conversion from this identity to the discrete coefficient norm, including the unit-count discrepancy and the small-index Möbius remainder, is the [Mellin–Plancherel bound](../../round4/density/MELLIN_LOW.md) and its [tighter discrete splitting](../../round5/kernel/MIXED_LOW.md).

Take \(e\in[l,u]\) and \(t\in[a,b]\), with \(l\ge0\). The whole segment joining \(z\) to \(z_0=(l+u)/4+i(a+b)/2\) lies in the closed right half-plane. Hence \(|A'(w)|\le\int_0^1 v\,dv=1/2\) along its dilate by \(W\), and
\[
 |A(Wz)|\le |A(Wz_0)|+\frac W2\sqrt{((u-l)/4)^2+((b-a)/2)^2}.
\]
The scalar \(A(Wl/2)\) is a second upper bound. Define \(r_0=\exp(-Wu/2)\) and \(r_1=\exp(-Wl/2)\). On a box with \(a^2+(l/2)^2>0\), a third bound follows from
\[
 |A(Wz)|^2\le
 \frac{(1-r_0)^2+4r_1\max_{a\le t\le b}\sin^2(Wt/2)}
 {W^2(a^2+(l/2)^2)}.
\]
The program takes the minimum. At the origin the first two bounds remain available. The removable denominator \(z\zeta(1+z)\) on \(b\le1/4\) is enclosed with the established \(N=16\) Euler–Maclaurin remainder. Above this point direct complex balls for \(\zeta(1+z)\) and the Euler factors bound the denominator away from zero, subdividing if needed. Integrating the full rectangle upper bounds on \(0\le t\le100\), then appending the previously proved reciprocal-zeta tail on \(t>100\), gives the certified \(I_e\). The frequency grid has 2048 subdivisions per unit through 1, 128 through 4, 32 through 12, and 16 through 100. The proof uses every real height and exponent.

On a finite logarithmic-height slab \(U\le\log T\le V\) the lowest surviving \(e\)-cell may start at \(\max(l,2\delta/V)\). All its subsequent factors keep the older conservative upper endpoint \(u\). The right Hilbert part, local signed-divisor squares, tail and discrete Möbius costs are as before. The function **mellin_bridge.right** is the tightened finite-slab entry point. It works with the original \(f_{2310}\); the centre, angular and horizontal sides of the detector rectangle use the same function.

For \(U=37,V=37.5,\delta=1,W=9.5,\log h=-3\), the 128-cell right constant is below \(0.00373113\). The previous integral enclosure gives \(0.00386208\) with the same parameters. The angular edge is bounded by \(243.787758\) in both computations.

**mellin_bridge.py** runs the exact physical-grid verifier with an isolated copy of its function namespace in which only the finite right-mean provider is replaced. The left-mean construction is unchanged. The flag **--old --diagnose** reruns the original provider on the same grid. All source files of the previous verification remain available.

At 160 bits, on the closed interval \(146.7\le L\le147.21\), the default refined verifier returns a total below **.993502**. With the original right mean the total is between **1.011598530** and **1.011598532** on the same grid. Both maxima are in the first physical cell. The height partitions have 80 physical-height samples per half-unit, 128 right exponent cells, and terminal log height 46. The physical mesh is \(1/96\). The seven fixed parameter triples are listed in **mellin_bridge.PARAM**. The new interval overlaps the established interval starting at 147.2. Under the same upstream assumptions this proves the pointwise assertion for each \(n\ge8\,467\,400\,925\,575\,746=\lceil e^{146.7/4}\rceil\).

Run in this directory:

~~~powershell
python -B mellin_bridge.py
python -B mellin_bridge.py --old --diagnose
~~~

The optional **midpoint=True** integral in mellin_sharp.py also bounds the first unit frequency band by the midpoint rule. For each real \(s=e/2\) the analytic function of complex \(t\) is \(F(s+it)F(s-it)\), where \(F=A(Wz)/(z\zeta_Q(1+z))\). Nonvanishing on the rectangles containing both radius-\(R\) disks is checked by interval arithmetic, using real symmetry for the lower disk. If \(|F|\le M\) on both, Cauchy's bound gives \(|(F(s+it)F(s-it))''|\le 2M^2/R^2\) throughout the real frequency cell. Its midpoint-rule error is at most \((b-a)^3M^2/(12R^2)\). This optional formula is outside the default bridge calculation.
