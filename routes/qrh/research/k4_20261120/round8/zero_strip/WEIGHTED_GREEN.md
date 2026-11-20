# A cosine-weighted hinge at the physical frequency

Assume QRH(7/8) and the existing moment and verified-height inputs. Put \(x=e^L,\ d=\log(1+4e^{-L/4}),\ \omega=L+d/2,\ H=3000175332800,\ T=H e^{7/4}\). The [spatial weight](../../round7/spatial/PROFILE.md) is a nonnegative symmetric probability density on \([0,1]\). For the second true height rectangle and \(143\le L\le144\), \(\gamma d<1\) for every \(H<\gamma\le T\). Hence its centered undamped cosine transform is between zero and one there. For each such positive root and its conjugate, the normalized signed zero contribution is bounded above by
\[
 2e^{(\beta-1)L}\big[(\cos(\omega\gamma))_+ + d\big].
\]
Indeed the exact multiplier is the integral of \(e^{(\beta-1)du}e^{i\gamma du}\) against this probability. Removing the damping costs at most \(d\) since \(0\le1-\beta\le1\), and removing the shift \(1/2\) produces the stated physical phase. The damping cost is common to the ordinary and phase-weighted comparison and is needed only once in a complete calculation.

## Two boundary sources

For \(a<b\le\Theta=7/8,\ \omega>0\), choose \(0<\epsilon\le1,\ \epsilon\sinh(\omega(b-a))\le\omega(b-a)\). Put \(C=\epsilon e^{\omega(b-a)}\) and
\[
 B(\sigma)=(\sigma-a)_++C(\sigma-b)_+,\qquad
 K(\sigma)=
 \begin{cases}
  0,&\sigma<a,\\
  \sinh(\omega(\sigma-a))/\omega,&a\le\sigma\le b,\\
  K(b)e^{-\omega(\sigma-b)},&\sigma\ge b .
 \end{cases}
\]
The function \(\Psi(\sigma,t)=B(\sigma)+\epsilon K(\sigma)\cos(\omega t)\) is nonnegative on the full complex plane. This follows by monotonicity of \(\sinh x/x\) before \(b\); afterwards \(K\) decreases and \(B\) increases. Away from \(a,b\) it is harmonic. Computing the two jumps in its normal derivative gives the distributional identity
\[
 \Delta\Psi=(1+\epsilon\cos(\omega t))\delta_a+
                     C(1-\cos(\omega t))\delta_b.
\]
In particular the two vertical source weights are nonnegative. For \(\sigma\le\Theta\) and \(-1\le z\le1\),
\[
  B(\sigma)z_+\le k[B(\sigma)+\epsilon K(\sigma)z],\qquad
  k=\max\left\{\frac1{1+\epsilon},
                \frac{B(\Theta)}{B(\Theta)+\epsilon K(\Theta)}\right\}<1. \tag{1}
\]
For \(z\ge0\) the worst ratio occurs at \(z=1\). The first ratio inside the maximum bounds \([a,b]\); the second bounds \([b,\Theta]\). The \(z<0\) assertion follows by nonnegativity of \(\Psi\).

## A closed finite rectangle

Fix one real-coefficient detector polynomial and the same Euler mollifier on both lines. Its determinant \(D=P(f)\) has all zeta zeros among its zeros, with at least the radial table's prescribed multiplicity \(\mu\). It is holomorphic on the rectangle and has no zeros on the right vertical edge \(\sigma=2\), where \(\log D\) uses its branch close to zero. Freeze the height used in the mollifier at \(T+.1\). Choose \(H'\in[H-.1,H)\) and \(T'\in(T,T+.1]\) with both \(\omega H'\) and \(\omega T'\) integer multiples of \(\pi\). This is possible since \(\pi/\omega<.1\). The bottom still lies above \(3\cdot10^{12}\); the extra low slice is harmless by positivity.

Write \(u=\log|D|\), and \(v=\arg D\) continued from the right along either horizontal edge. Green's formula on \([a,2]\times[H',T']\) expresses \(2\pi\sum_\rho\Psi(\rho)\) for the determinant as the sum of the two source integrals above and its three edge terms. Equivalently extend \(\Psi\) by zero across \(a\) and take the rectangle's left edge slightly to its left; the derivative jump then supplies exactly the source on \(a\). At the horizontal edges use \(u_t=-v_\sigma\) and integrate by parts. The term \(\Psi_t u\) vanishes there because the sine is zero. The two remaining integrals are signed copies of \(\int_a^2\Psi_\sigma v\,d\sigma\). On the right \(u_\sigma=v_t\); integrating by parts there leaves \(-\int_{H'}^{T'}(\Psi_t v+\Psi_\sigma u)\,dt\). Its endpoint terms exactly cancel the two horizontal corner terms, since all three branches agree at the right corners.

Both \(|\Psi_\sigma|\) on the horizontal edges and \(|\nabla\Psi|\) on the right are at most
\[
 M=1+C+\epsilon\cosh(\omega(b-a)).
\]
Thus after division by \(2\pi\mu\), the combined edge cost is bounded by \(M\) times the existing absolute angular and right-edge certificate evaluated at the frozen height. The right log bound controls its complex modulus, so the two right terms together cost at most \(M|\log D|\). The Jensen disks are within the earlier height allowance, and the original angular estimate bounds the absolute value at each horizontal abscissa before integrating. [Absolute Jensen and right-edge bounds](../../round6/reduction/tables.py)

If a horizontal passes through a determinant zero, apply the identity first at nearby generic heights with the determinant frozen. In the limit \(\Psi_t=O(|t-t_0|)\) uniformly on the compact horizontal range, and \(\int|\log|D||\,d\sigma\) is locally uniformly bounded by factoring out the finitely many zeros in a compact neighborhood. The Jensen angular estimate is uniformly valid. Since \(H'<H<T<T'\), every target zero remains strictly between the boundaries in this limiting argument. Zeros at \(a\) have zero weight, and zeros at \(b\) cause only an integrable singularity at the vertical source. The argument also follows by regularizing \(\log|D|\) near the finitely many zeros. Extra determinant zeros cost nonnegative mass.

## Cosine-weighted interpolation for the source integrals

Use \(\ell=1/2,\ r=1+\delta/\log(T+.1)\), and the same decaying analytic function \(F(z)=g(z)(z-1)f(z)/z\) as in the [flat-window proof](../../round2/spectrum/PROOF.md). For \(n\in\{a,b\}\), let \(\theta=(r-n)/(r-\ell),\ p_\ell=4/3,\ p_r=2,\ 1/\nu=\theta/p_\ell+(1-\theta)/p_r,\ P=\theta\nu/p_\ell\). Denote the two probability kernels obtained by normalizing the left and right harmonic measures in the strip by \(P_\ell,P_r\). The subharmonic inequality for \(\log |F|\), followed by Jensen on the two boundary measures, gives the pointwise estimate
\[
 |F(n+it)|^\nu \le
    [P_\ell*|F(\ell+i\cdot)|^{4/3}(t)]^P
    [P_r*|F(r+i\cdot)|^2(t)]^{1-P}.
\]
This follows first on finite strips by the maximum principle, or by adding a small positive constant to the edge moduli before taking logarithms. The horizontal ends have uniformly decaying \(F\), giving the infinite-strip formula on letting the ends escape. For \(w(t)=1+\eta\cos(\omega t),\ |\eta|\le1\), multiply by \(w\), integrate, and apply Hölder on the positive measure \(w(t)dt\). The two boundary integrals get weights \(P_\ell*w\), \(P_r*w\). At frequency \(\omega\), their respective cosine factors are
\[
 q_\ell=\frac{\sinh((r-n)\omega)}{\theta\sinh((r-\ell)\omega)},\qquad
 q_r=\frac{\sinh((n-\ell)\omega)}{(1-\theta)\sinh((r-\ell)\omega)}.
\]
These follow by solving the elementary harmonic Dirichlet problem for a cosine prescribed on just one boundary. Consequently the unweighted interpolation bound increases by at most
\((1+|\eta|q_\ell)^P(1+|\eta|q_r)^{1-P}\). This handles the noninteger exponent without shifting any fractional powers of \(f\). The real-coefficient and cosine symmetries permit integration over the whole real line and division by two. Positivity permits restricting the resulting bound to \([H',T']\). On that interval the previous factor \(N=(1+10^{-6})^2/(1-1/(3\cdot10^{12}))\) transfers \(F\) to \(f\). The proof applies to every fixed determinant in the radial table, so its radial constants at \(a,b\) must be obtained from the same table row. The scalar estimate for an unpaired remainder may separately minimize over that table.

## Relation to physical chord terms

At equally spaced real-part nodes, of step \(g\), the coefficient of \((\beta-a)_+\) in the piecewise linear upper interpolant of \(e^{(\beta-1)L}\) is \(c_a=e^{(a-1)L}2[\cosh(gL)-1]/g\). Nodes \(a,b\) have coefficient ratio \(e^{L(b-a)}\). If this ratio is at least \(C\), apply (1) to the two terms with coefficients \(c_a,Cc_a\), and use the ordinary bound on the remaining \(c_a[e^{L(b-a)}-C](\beta-b)_+\). All other terms can retain their ordinary bounds. Since the actual spatial contribution is at most its positive cosine times the interpolant, this produces a strict saving on these two actual nonnegative chord coefficients when the new numerical upper bound is below the old one. Multiply by two for the conjugate roots.

The numerical trial uses \(a=.865,\ b=.870,\ \epsilon=.9,\ L=143\), and the unchanged mollifier with \(\delta=1.1,\ W=8.5,\ \log h=-2.25,\ Q=2310\). It compares the ordinary and paired source estimates on \(H<\gamma\le T\), with the same source norm inputs. It does not assert a new covered fourth-power endpoint.

~~~powershell
python -B weighted_green.py
~~~

2026-11-20. Joint project attribution to Claude and Codex.
