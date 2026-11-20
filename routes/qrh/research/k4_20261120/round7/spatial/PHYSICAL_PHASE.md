# Several harmonic sources at the physical frequency

Write \(d=\log(1+4e^{-L/4})\), \(\omega=L+d/2\) and \(x=\omega(\sigma-a_0)\). The spatial polygon is symmetric about its midpoint. Its centered, undamped Fourier transform is real. In [signed_profile.py](signed_profile.py) its two signs are bounded separately. The second derivative of the transform is bounded by the second moment of the polygon, and the second derivative of the numerator of \(y^2\widehat\phi(y)\) by the sum of the absolute second-difference coefficients times their squared frequencies. On each mesh interval take the endpoint maximum with its interpolation error and then successive maxima to the right. The numerator and transform use the same coefficients as [the height proof](PROFILE.md). Applying the lower endpoint version to the transform proves nonnegativity through \(y=8.32421875\). The exact damped transform differs from the centered undamped expression, apart from the midpoint phase, by at most \(d\) per weighted zero, as in the [two-source proof](../../round8/zero_strip/WEIGHTED_GREEN.md).

## A positive comparison on all ordinates

Fix integer modes \(m\ge1\), \(x_i=ih\), positive weights \(w_i\), and \(B(x)=\sum_i w_i(x-x_i)_+\). For \(x\ge0\) let
\[
 G_m(x,a)=-\frac{e^{-m|x-a|}-e^{-m(x+a)}}{2m},\qquad
 F_m(x)=\sum_{i>0}d_{im}G_m(x,x_i).
\]
Set \(F_m=0\) on \(x<0\). Its derivative jump there is \(d_{0m}=-\sum_{i>0}d_{im}e^{-mx_i}\). At every other knot its derivative jump is \(d_{im}\). With \(y=\omega t\), put \(\Psi=(kB+\sum_m F_m\cos(my))/\omega\). Its vertical sources in the \((\sigma,t)\)-plane have densities \(kw_i+\sum_m d_{im}\cos(my)\). Thus one fixed determinant on the rectangle bounds this entire comparison, including all modes, with the same horizontal and right-boundary argument as for two sources. The reference \(B/\omega\) is the sum of the physical hinges \(w_i(\sigma-a_i)_+\).

[The verifier](angular_certificate.py) rounds a floating-point linear program's proposed coefficients to rationals, enforces the origin identity with intervals, and increases \(k\) until two inequalities hold. First, every source density must be nonnegative on the complete angular circle. Second, for every \(0\le x\le nh\) and every angle the numerator of \(\Psi\) must be at least \(B(x)(\cos y)_+\) in the positive case or \(B(x)|\cos y|\) in the absolute case. Beyond \(nh\) the periodic harmonic function is nonnegative by the minimum principle on the cylinder: at \(nh\) the comparison gives a nonnegative value, and at infinity its affine part grows with positive slope while every other term decays.

The two angular branches meet at \(\pi/2\), a mesh point. Linear interpolation in angle has error at most the squared step times a uniform second derivative bound divided by eight. On a space cell contained between knots, \(F_m''=m^2F_m\); its absolute value attains its maximum at an endpoint. Interpolate the dimensional inequality, using the smaller endpoint of \(B\) in the curvature remainder. At the first knot use \(F_m(x)/B(x)=d_{0m}\sinh(mx)/(w_0mx)\), with the quotient continued at zero. Its second derivative is bounded by \(|d_{0m}|m^2\cosh(mh)/w_0\) by the integral representation of sinhc. This also covers the exact first endpoint. For a physical interval use the full interval for \(h=\omega g\) and exact \(w_i=\exp(ig L_{\min})\), where \(g\) is the spacing in real part.

The half-plane kernel satisfies \(|\partial_x G_m|\le1\) on each smooth piece and \(m|G_m|\le1\). In \(\sigma,t\) units the Euclidean gradient of its cosine extension divided by \(\omega\) is therefore at most one. Thus all three edge errors together can use the ordinary angular edge bound multiplied by \(k\sum w_i+\sum_{i>0,m}|d_{im}|\). The horizontal levels can be chosen at common multiples of \(\pi/\omega\). For a source with constant \(b=kw_i\), Poisson convolution and Hölder give the two factors
\[
 \left(b+\sum_m |d_{im}|q_{\ell,m}\right)^P
 \left(b+\sum_m |d_{im}|q_{r,m}\right)^{1-P}.
\]
The harmonic multipliers \(q_{\ell,m},q_{r,m}\) use frequency \(m\omega\). All line contributions and the edge must use the same detector before minimizing.

## A price on actual cumulative zeros

For \(143.4\le L\le143.41,\ T=e^{36}\), take the fourteen real parts .833,.836 through .872 and modes 1, 2, 3. The polygon is positive on the whole ordinate range through \(T\). The zero-cost comparison above has a common scalar source coefficient below .828823. With the same three unshifted taper choices as the two-source calculation, including both horizontal sides, the right boundary, and a common radial polynomial for each candidate, the full upper bound on these fourteen hinges is below 164827316. The corresponding sum of separately minimized ordinary hinge bounds after convexification is above 178045448. The ratio is below **.925760**. These values refer to one weighted height sum; establishing a fourth-power endpoint requires the remaining heights, real-part nodes, prime powers, damping and tails. The source table and its recomputation are recorded in the [full two-source calculation](../../round8/zero_strip/COMPLETE_GREEN.md).

~~~powershell
python -B round7/spatial/angular_certificate.py --upper .833
python -B round7/spatial/angular_row.py --upper-ratio .925760
~~~

## A translated low-height window

The same comparison can be used on a translated low-height window. Let the signed Logan test have bandwidth \(K\), mass \(I\), and Gaussian width \(Q\). Normalize its undamped spectrum to \(V(t)=\sin(a(1-|t|/K))/\sin a\) inside the band, and zero elsewhere. It is nonnegative and Lipschitz with constant \(a/(K\sin a)\). For \(|b|\le1/2\) and a Gaussian \(X\) of variance \(2Q^2\), the complex convolution multiplier is \(e^{b^2/(4Q^2)}e^{ibX/(2Q^2)}\), with mean one. Subtracting \(V(\gamma)\) therefore leaves an absolute error at most \(2Qa e^{1/(16Q^2)}/(K\sqrt\pi\sin a)\). The physical contribution of each conjugate pair can charge its main part against \(V(\gamma)(\cos(\gamma c))_+\). Zeta symmetry moves the reflected real part to its matching term in the weighted sum. The Gaussian remainder uses the ordinary cumulative envelope.

For a cumulative height \(H+D\), freeze the translated test on \([H,H+D+1]\). Pick cosine extrema for both horizontal edges, the lower in \((H,H+.1)\), the upper in \((H+D,H+D+.1)\). Cover the short omitted interval by the explicit Riemann–von Mangoldt increment times \(e^{-L/8}\). The [translated half moments](../first_selected/SELECTED.md) are doubled on both boundaries before using the full-line Poisson proof; translation may destroy evenness of the auxiliary window. Since the radius scale is \((D+1)/2\), the right-edge length multiplier is two, and the Jensen circles use the actual height \(H+D+1\). Use nonnegative chord coefficients for the remaining hinges. The [replay](../first_selected/near_phase.py) with \(K-H=24\cdot10^9\) and three height panels on \([115.402,115.412]\) gives .009334925 including a Gaussian error below \(5.101\cdot10^{-9}\). Four panels at \(16\cdot10^9\) give .005349435. Finer ordinary height covers currently give smaller bounds on these two tests.

## Spatial autocorrelation trial

For positive symmetric step data \(H_j\) on the two halves of \([-1/4,1/4]\), normalize the step function \(f\) to mass one and take \(\phi=f*f\). Its centered transform is \(\widehat f^2\ge0\). Cauchy gives peak \(\int f^2=2n\sum H_j^2/(\sum H_j)^2\) at zero. The step width is \(w=1/(4n)\). The numerator of \(y\widehat f(y)\) is the sine polynomial with coefficients \((H_j-H_{j+1})/(w\sum H)\) at positive step edges. Its squared total coefficient norm bounds \(y^2\widehat\phi(y)\). Damping the transform leaves the same inverse-square tail: the distributional second derivative of the convolution is \(df*df\); integrating against the exponentially damped mode gives the variation bound divided by the squared modulus of its complex frequency (on the uncentered unit interval the damping has modulus at most one). [The verifier](autocorrelation.py) also bounds the two interpolation curvatures. At the test slab \([143.95,143.951]\), both the triangle and the two-height shoulder variant had complete upper costs above one. The signed polygon remains available for that comparison.
