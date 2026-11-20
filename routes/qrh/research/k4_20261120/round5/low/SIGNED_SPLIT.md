# Removing the left zeros from the signed vertical integral

For every one of the [30 finite-density rectangles](../kernel/GRID_TARGET.md), let \(s,T,\Delta=T/100,V=T+\Delta,Y=512V,K\) and \(D=D_Y\) be as in the [signed contour reduction](../spectrum/SIGNED_CONTOUR.md). The normalization below is the same. Put \(w(t)=W(|t|)\), the even extension of its trapezoid. Take \(s<\eta<(1+s)/2\) while avoiding zero poles on the finite segment. Write
\[
 K_\rho(t)=\frac1{\eta+it-\rho}-\frac1{2+it-\rho},\qquad
 \mathcal L(F)=\frac1{4\pi}\Re\int_{-V}^{V} w(t)D(\eta+it)F(t)\,dt.
\]
Let \(\mathcal R\) be the finite set, with multiplicities, of nontrivial zeros with \(\beta>s,\ H<|\gamma|\leq V\). Then
\[
 J:=\mathcal L\!\left(\zeta'/\zeta(\eta+i\,\cdot)\right)
   =\frac12D(1)+\mathcal L\!\left(\sum_{\rho\in\mathcal R} K_\rho\right)
                 +E,\qquad |E|<0.030834,\quad |E|/K<1.0350\,10^{-8}.                 \tag{1}
\]
This is an upper bound on contributions of the *actual* complementary zeros, uniform as \(\eta\downarrow s\). In particular the aggregate absolute error for all zeros with \(\beta\leq s\), counted after their individual time integrals, is below \(0.000255\). The residual in (1) is unknown. The original pole term cancels when (1) is inserted into the argument principle. It is sufficient to bound the limsup of the finite signed residual by \(0.91646K\) at the 30 rectangles. [Numerical certificate](signed_split.py)

## Positive Fourier frequencies on the reference line and at left zeros

Real coefficients turn \(J\) into the half-axis integral in the signed contour paper. Write \(D(z)=\sum_{n>N}a_n n^{-z}\), where \(N=32768\) and \(a_n\) here includes the normal CDF. Set \(S=\sum_{n>N}|a_n|n^{-s}\). With \(u=\log Y,\ b^2=2(3/8)^2,\ z=1-s+1/u\), the [Gaussian coefficient estimate](../left/large_values/GAUSSIAN.md) gives
\[
 S\leq Y^z e^{z^2/(2b^2)}(1+u)^2.
\]
Indeed before the CDF the coefficients have modulus at most \(d(n)\), the CDF is at most \((Y/n)^z e^{z^2/(2b^2)}\), and \(\zeta(1+1/u)^2\leq(1+u)^2\). Let \(\omega=\log n>\omega_0=\log N>10\). The even trapezoid has transform
\[
 \widehat w(\xi)=2[\cos(T\xi)-\cos(V\xi)]/(\Delta\xi^2).
\]
Absolute convergence on \(\Re z=2\) therefore makes \(|\mathcal L(\zeta'/\zeta(2+i\,\cdot))|\leq S/(\pi\Delta\omega_0^2)\): the frequencies are \(\log(nm)>0\), and \(-\zeta'(2)/\zeta(2)<1\).

Subtract the logarithmic derivatives of the completed zeta function at \(\eta+it\) and \(2+it\). The Hadamard product gives the sum of \(K_\rho\) over all nontrivial zeros. Absolute convergence at large \(|\gamma|\) follows from \(K_\rho=O(|\gamma|^{-2})\) on the compact segment and Riemann–von Mangoldt. The digamma series, together with the two rational factors of the completed function, gives the exact difference
\[
 \frac{\zeta'}{\zeta}(\eta+it)-\frac{\zeta'}{\zeta}(2+it)
     =\sum_{\rho}K_\rho(t)+\sum_{k\geq1}K_{-2k}(t)-K_1(t).
\]
In fact the \(k=0\) term of the digamma expansion cancels the rational term from \(z=0\). [Completed derivative and Poisson sum](../left/large_values/GAUSSIAN.md)

For each zero with \(\beta\leq s\), write \(a=\eta-\beta>0,\ d=2-\beta\in[1,2]\). Its difference kernel has the one-sided representation
\[
 K_\rho(t)=\int_0^\infty(e^{-av}-e^{-dv}) e^{i(\gamma-t)v}\,dv .
\]
Thus after multiplying by \(n^{-it}\) the transform of \(w\) is always evaluated at \(\omega+v\), bounded away from zero. Expanding the two cosines leaves four endpoint integrals, each multiplied by a unit complex phase and \(1/\Delta\), of the form
\[
 I(\lambda)=\int_0^\infty F(v)e^{i\lambda v}\,dv,\qquad
 F(v)=\frac{e^{-av}-e^{-dv}}{(\omega+v)^2},\qquad
 \lambda=\gamma\pm T\ \hbox{or}\ \gamma\pm V.
\]
The factor \(F\) vanishes at zero, while \(\int|F|\leq1/\omega\). Since \(0<a<d\leq2\), \(|F'(0)|\leq2/\omega^2\), and
\[
 \int_0^\infty |F''(v)|\,dv\leq4/\omega^2+10/\omega^3.
\]
The three terms in the Leibniz estimate come from the second derivative of the numerator (integral at most \(a+d\)), its first derivative (integral at most 2), and its modulus (at most 1). Two integrations by parts, together with the \(L^1\) bound, therefore give
\[
 |I(\lambda)|\leq\min\{1/\omega,7/(\omega^2\lambda^2)\}
     \leq\frac{2}{\omega(1+\lambda^2)}
     \leq\frac4\omega\,\frac{d}{d^2+\lambda^2}.
\]
This estimate remains uniform for \(a\downarrow0\). The [signed contour Poisson estimate](../spectrum/SIGNED_CONTOUR.md) is at most \(A=\frac12\log(2T)+3\) at each of the four endpoints; symmetry handles negative heights. Summing the four terms, the left zeros and the Dirichlet coefficients gives the cost \(4AS/(\pi\Delta\omega_0)\). All absolute values here are taken *after* the time integral for the individual frequency and zero. Pointwise absolute values of the original log derivative have a different size.

For the trivial zeros, combine their identical ordinates in their one-sided Laplace representation. Their combined numerator is
\[
 (e^{-\eta v}-e^{-2v})\,e^{-2v}/(1-e^{-2v})
        \leq (2-\eta)e^{-\eta v}/2 .
\]
This uses \(1-e^{-2v}\geq2v e^{-2v}\) and the mean value theorem in the exponent. Consequently their cost is at most \(S(2-s)/(2s\pi\Delta\omega_0^2)\).

The pole at 1 is to the right of \(\eta\). For \(\omega>0\), the full-axis transform of \(K_1\) at \(\omega\) equals \(-2\pi e^{-(1-\eta)\omega}\), by its single pole below the real \(t\)-axis; the reference factor has no pole below. This transform is absolutely integrable in \(t\) for the difference kernel. Restoring \(w\) costs at most \(2(2-s)/T\) per Dirichlet frequency, since the change is supported on \(|t|\geq T\) and \(|K_1(t)|\leq(2-s)/t^2\) there. Hence \(-\mathcal L(K_1)=D(1)/2+O(S(2-s)/(2\pi T))\) with constant 1.

## Eliminating the exterior ordinates

For \(|\gamma|>V\), set \(g=|\gamma|-V\). By symmetry it suffices to put \(\gamma>V\) and \(x=\gamma-t\); then \(x\geq g\). For \(0<g<1\),
\[
 |K_\rho(t)|\leq\frac{2-s}{x\max(1,x)},\qquad
 w(t)\leq (V-t)/\Delta\leq x/\Delta.
\]
Integrating up to \(x=g+2V\) costs at most \((2-s)(1+\log(2V+1))/\Delta\). Both exterior boundary layers together contain at most \(5A\) zeros, from the Poisson bound at \(\pm V\) and \(d/(d^2+x^2)\geq2/5\) for \(d\in[1,2],\,|x|\leq1\).

For \(g\geq1\), the difference of the two rational factors gives
\[
 |K_\rho^{(j)}(t)|\leq(j+1)!(2-s)x^{-j-2},\qquad j=0,1,2 .
\]
The second distributional derivative of \(wK_\rho\) has three terms. Its \(w''K_\rho\) term costs at most \(4(2-s)/(\Delta g^2)\) from the four slope jumps. The \(2w'K_\rho'\) term costs at most \(2(2-s)/(\Delta g^2)\). For \(wK_\rho''\) use \(w\leq(x-g)/\Delta\) and \(\int_g^\infty(x-g)x^{-4}\,dx=1/(6g^2)\). Two integrations by parts bound the per-zero, per-frequency transform by \(7(2-s)/(\Delta\omega^2 g^2)\). Finally \(1/g^2\leq4d/(d^2+g^2)\) for these \(g,d\). Summing the Poisson bounds at the two endpoints gives an exterior cost
\[
 \frac{14(2-s)AS}{\pi\Delta\omega_0^2}
       +\frac{5A(2-s)S(1+\log(2V+1))}{4\pi\Delta}.
\]
The first term comes from \(g\geq1\); the second from \(0<g<1\). Only the subset \(\beta>s\) is needed here, so no earlier contribution is subtracted. Finite-height RH puts all \(|\gamma|\leq H\) on the critical line. This leaves exactly the finite residual in (1).

## Smooth von Mangoldt truncation and the count

The absolutely convergent reference series can also be truncated with weight \((1-m/M)_+\), \(M=2^{40}\). The error in its normalized integral is at most the reference bound times \(5/\sqrt M\). Indeed the weight defect is at most \(\sqrt{m/M}\) and \(\sum\Lambda(m)m^{-3/2}\leq\sum_{m\geq2}(\log m)m^{-3/2}<5\) by the decreasing integral. The truncation error is below \(1.64\,10^{-12}\). A compactly supported infinitely differentiable cutoff equal to 1 through \(M/2\), zero from \(M\), and valued in \([0,1]\) has defect at most \(\sqrt{2m/M}\), so its error is below \(2.32\,10^{-12}\). For instance, with \(h(x)=e^{-1/x}\) for \(x>0\) and zero otherwise, use \(h(1-x)/(h(1-x)+h(x-1/2))\) at \(x=m/M\). If the tapered prime polynomial is subtracted on the original line instead, its own normalized integral has absolute value at most
\[
 \frac{S}{4\pi\Delta\omega_0}
          \left(1+\frac{M^{1-s}-1}{1-s}\right)<0.001139 .
\]
Use \((\omega+\log m)^2\geq4\omega\log m\), \(\Lambda(m)\leq\log m\), and integral comparison. This optional subtraction leaves the finite unknown zero residual; it was not used in (1).

The left zeros, reference line, trivial zeros, pole tail and exterior right zeros sum to an absolute error below \(0.030834\) over all thirty parameter choices. In the [averaged argument principle](../spectrum/SIGNED_CONTOUR.md) the pole contribution is \(-D(1)/2\) on the lower bound for \(-\Re\sum D(\rho)\); it cancels the \(+D(1)/2\) in (1). Replacing the old absolute pole allowance (greater than 1 per rectangle) by \(0.030834\) therefore preserves the previously certified sufficient fraction \(0.91646\). The bound for the remaining finite signed sum has not been proved.

~~~sh
python -B round5/low/signed_split.py
~~~
