# A quadratic signed vertical-integral criterion

This is a conditional reduction for the same thirty \((s,T)\) targets as the [linear signed-contour calculation](../../spectrum/signed_contour.py). Codex derived the quadratic and two-scale estimates under the workspace's joint Claude/Codex attribution protocol. No bound for the final vertical integral is assumed as an established input.

Fix \(s=.800,.820,.837,.852,.865\) and \(T=H e^{k/4}\) with \(k=1,4,9,17,30,51\). Put \(V=1.01T,\Delta=V-T,Y=512V,\ p=3(1-s)/(3s-1),\ R=6(\log T)T^p\). Set \(W(t)=1\) on \([0,T]\), \(W(t)=(V-t)/\Delta\) on \([T,V]\), and \(W=0\) above \(V\). Let \(D_Z\) be the [Gaussian signed tail](GAUSSIAN.md) with \(Q=210,N=32768,b^2=2(3/8)^2\). Choose \(0\le h\le4\), write \(D_\pm=D_{Y e^{\pm h}}\), and define the analytic detector
\[
 F(z)=(1+D_-(z))(1+D_+(z))-1 .
\]
When \(h=0\), \(F=2D_Y+D_Y^2\). All coefficients are real. The unresolved sufficient condition on each row is
\[
 \limsup_{\eta\downarrow s}\frac1{2\pi}\Re
       \int_0^V W(t)F(\eta+it)\frac{\zeta'}{\zeta}(\eta+it)\,dt
       \ \le\ c_* R.                                           \tag{1}
\]
One may use \(c_*=.98643\) in all thirty rows for \(h=0\), or \(c_*=.98806\) in all rows for \(h=5/2\). Either set of thirty inequalities would imply the associated thirty count targets. The right limit, taken off zeros, is important when \(\beta=s\) occurs.

## Residues and critical errors

Apply the residue theorem to \(F(z)\zeta'(z)/\zeta(z)\) in the rectangle \(\eta\le\Re z\le2,\ |\Im z|\le U\), for almost all \(T<U<V\). The full pole residue at 1 is \(-F(1)\); after division by two the corresponding term in the formula for the sum of \(\Re F(\rho)\) at positive ordinates is \(F(1)/2\). Every nontrivial zero inside contributes its multiplicity times \(F(\rho)\). No trivial zero is inside. At any such zero, \(\Re F(\rho)\le-1+|(1+D_-(\rho))(1+D_+(\rho))|\).

For a zero with \(d=\beta-\tfrac12\), put \(x_\pm=e^{\pm dh}I_{\rho,\mathrm{near}}(Ye^{\pm h})\) with truncation \(|v|\le40\). The common normalization is \(Y^{-d}\). The [weighted Gaussian Gram argument](JOINT_SCALES.md), valid also for the [optimized reflected Poisson prefactor](../../spectrum/REFLECTION.md), gives
\[
 (x_-,x_+)^*G^{-1}(x_-,x_+)\le E_\rho,\quad
 G=\begin{pmatrix}1&g\\g&1\end{pmatrix},\quad g=e^{-b^2h^2}.
\]
Here the sum of \(E_\rho\) over all zeros under consideration up to \(V\), divided by \(R\), is bounded by the expression used in the script before its factor \(1+10^{-12}\) and \( (1+g)/2\). It is the original reflected Gaussian count ratio, multiplied by \((1/2-10^{-40})^2 R_s(V)/R\), to undo the previous threshold and \(R_s(V)=7\log(V)V^p\) normalization. The identity depends on the frequency kernel being bounded **pointwise** by a multiple of a Gaussian times the Poisson pair. The optimized reflected proof supplies exactly such an inequality. If \(h=0\) the scalar estimate is used directly.

The top eigenvalue of \(G\) is \(1+g\); hence \( |x_-x_+|\le (|x_-|^2+|x_+|^2)/2\le (1+g)E_\rho/2\), and each \(|x_\pm|\le\sqrt{E_\rho}\). Replacing \(x_\pm\) by \(e^{\pm dh}(1+D_\pm(\rho))\) changes each coordinate by less than \(10^{-27}\), using the horizontal-tail, Gaussian weight and pole estimates uniformly for \(|h|\le4\). The exponential factors cancel in the product. Since \(2\cdot10^{-27}\sqrt E\le 10^{-13}E+10^{-40}\), the product is at most \((1+10^{-12})(1+g)E_\rho/2+10^{-28}\). This avoids the square root in the error of the linear density criterion.

## Horizontal edges averaged over all heights

Put \(A=\frac12\log(2T)+3,\ r=1/32\). Write \(L_D(\sigma,Z)\) for the bound **mean_square** for the time mean of \(|D_Z(\sigma+it)|^2\) over an interval of length \(\Delta\), and \(S_\pm=L_D(s,Ye^{\pm h})\). Its analogue with the time interval extended to \([T-r,V+r]\) and the real part moved to \(s-r\) gives
\[
 U_\pm=\frac{1+2r/\Delta}{\pi r\log N}
       L_{D,\Delta+2r}(s-r,Ye^{\pm h}).
\]
For \(x\ge s\) the time mean carries an additional multiplier \(N^{-2(x-s)}\), because every Dirichlet index exceeds \(N\). The underlying Montgomery–Vaughan mean estimate uses \(|a_n|\le\tau(n)\), the Gaussian Chernoff majorant and \(\sum\tau(n)^2 n^{-u}\le\zeta(u)^4\). For the supremum over \(s\le x\le2\), apply the subharmonic disk mean of radius \(r\) to \(|D_Z|^2\). In the enlarged time interval Fubini gives time overlap at most \(2r\). The real-part integral of \(N^{-2(x-s+r)}\) contributes \(1/(2\log N)\). This gives the claimed \(U_\pm\).

The decomposition of \(\zeta'/\zeta\) on each top segment has a smooth part of modulus at most \(B=3+(2(2-s)+2.5)A\) and local simple poles from \(|U-\gamma|\le1\). This follows by comparing with \(2+iU\) in the partial fraction formula, using \(\sum_\rho P_{2-\beta}(U-\gamma)\le A\), where \(P_a(w)=a/(a^2+w^2)\). The count within radius one is at most \(2.5A\). The total count in \([T-1,V+1]\) is at most \((\Delta+4)A/.9\) by integrating \(P_{2-\beta}\) over \([T-2,V+2]\). A local singular factor integrated along the real segment costs at most \(2\log(4/|U-\gamma|)\). Thus the same linear bounds as in the source script give, before division by \(2\pi\), the two contributions
\[
 \frac{B}{\log N}(\sqrt{S_-}+\sqrt{S_+})
 +A\sqrt{\frac{2.5(\Delta+4)}{.9\Delta}\,8[(\log4)^2+2\log4+2]}
       (\sqrt{U_-}+\sqrt{U_+}).
\]
For the product term, the smooth part costs \(B\sqrt{S_-S_+}/(2\log N)\), by Cauchy and the extra exponential decay in \(x\).

To integrate the local singularities against \(|D|^2\), put their positive sum \(K(U)=\sum_{|U-\gamma|\le1}2\log(4/|U-\gamma|)\) *inside the same disk-mean Fubini argument*. At any \(t\in[T-r,V+r]\), only zeros at distance at most \(1+r\) enter; their number is at most \(mA\) for
\[
 m=\max\{1+(1+r)^2,\ 2+(1+r)^2/2\}<2.55.
\]
Indeed the reciprocal of each relevant Poisson kernel is bounded by \(a+(1+r)^2/a\), whose maximum on \(1\le a\le2\) is at an endpoint. The integral over \(t-r\le U\le t+r\) of each singular logarithm restricted to \(|U-\gamma|\le1\) is at most \(4r(\log(4/r)+1)\), attained by centering the interval. This gives a weighted mean-square bound \(2mA(\log(4/r)+1)U_\pm\). Apply Cauchy with this same nonnegative \(K(U)\) to the product \(D_-D_+\). The resulting contribution is \(2mA(\log(4/r)+1)\sqrt{U_-U_+}\). Neither part of the proof requires a fourth time moment for \(D_Y\).

## Pole and right edge

At \(z=1\) the Gaussian Mellin integral for the *full* sum has a double pole at zero, since both \(\zeta(1+w)\) and the Mellin kernel have a simple pole. Its residue is exactly \(P(1)(\log Z+\gamma)+P'(1)\). Moving the integral to \(\Re w=-1/2\) yields
\[
 |D_Z(1)|\le |P(1)(\log Z+\gamma)+P'(1)-1|
 +10^{-30}+\frac{6\cdot431\,e^{1/(8b^2)}}{\pi\sqrt Z}
       \big(\sqrt{2\pi}\,b+2b^2\big).
\]
Here \(1-\Phi(b\log Z)<10^{-30}\), and \(\sqrt{1+|v|}\le1+|v|\) majorizes the critical-line zeta bound. The coefficient sum \(\sum|\lambda_d|/\sqrt d<431\) was checked in the short detector. The finite sieve gives \(P(1)\simeq.0018149978042649,\ P'(1)\simeq.98242099488684\). For both scales the absolute pole contribution is at most \((d_-+d_++d_-d_+)/2\), with \(d_\pm\) the displayed bounds.

On \(\Re z=2\), the signed positive-height time integration of each Dirichlet term \(k^{-it}\) contributes at most \(1/\log k\) on taking the real part. All terms of \(F\zeta'/\zeta\) have \(k>N\). Their total absolute coefficient mass on this line is at most
\((2\zeta(2)^2+\zeta(2)^4)(-\zeta'(2)/\zeta(2))<10\).
This proves the right-edge charge. Integrability of the horizontal logarithmic singularities permits averaging over all heights. For \(\eta\downarrow s\), choose \(\eta\) below the nearest strictly larger zero real part up to \(V\); the finite set counted is then constant. The boundary zero with \(\beta=s\) stays outside. Fubini in the positive-height integral gives \(W(t)\) in (1).

If \(N_{>s}(T)>R\), all the rectangles up to \(V\) contain more than \(R\) positively indexed zeros. Averaging the residue formula and the critical error bound makes the left side of (1) exceed \(R\) times the row's computed available fraction. This proves the reduction.

| \(h\) | Minimum across 30 rows | Largest normalized critical cost | Largest normalized boundary cost |
|---:|---:|---:|---:|
| 0 | >.98643106 | <.00687933 | <.00757841 |
| 2 | >.98793074 | <.00455636 | <.00810158 |
| \(5/2\) | >.98806622 | <.00403274 | <.00842207 |
| 3 | >.98793878 | <.00371332 | <.00882766 |

Run **python -B quadratic_contour.py** for the one-scale calculation and **python -B quadratic_contour.py --spread 2.5** for the two-scale calculation. These are conditional vertical-integral criteria and provide no independent upper bound for the vertical integral in (1).

## Removing the signed contribution of a long prime polynomial

For \(h=5/2\), let \(B_M(z)=\sum_{m\le M}b_m m^{-z}\) with any real coefficients satisfying \(|b_m|\le\Lambda(m)\). The sign and taper of these coefficients may be chosen separately in each row. The contribution of \(F B_M\) to the real part in (1) is bounded absolutely at the following levels.

| \(M\) | Maximum signed cost divided by \(R\) | Common sufficient fraction after replacing \(\zeta'/\zeta\) by \(\zeta'/\zeta+B_M\) |
|---:|---:|---:|
| \(T^3\) | <.00002985 | .988065 |
| \(T^4\) | <.005663 | .987319 |

To see the sign cancellation, for every \(k>1\),
\[
 \int_0^V W(t)\cos(t\log k)\,dt
  =\frac{\cos(T\log k)-\cos(V\log k)}{\Delta(\log k)^2}.
\]
Since all coefficients are real, this is the full real-part kernel. All indices \(n\) of \(F\) satisfy \(n>N\). For \(d=1-s>0\) and \(H_P=\sum|\lambda_n|/n\), a bound for the absolute Dirichlet mass of \(D_Z\) on \(\Re z=s\) is
\[
 L_Z=H_P\,Z^d e^{d^2/(2b^2)}/d.
\]
Indeed expand \(\zeta P\) in its convolution and replace the inner sum over the positive integer \(m\) by the integral starting at zero: the function \(m^{-s}\Phi(b\log(Z/(nm)))\) is decreasing. This integral is \((Z/n)^d e^{d^2/(2b^2)}/d\) by the Gaussian moment formula. The mass of \(F\) is at most \(L_{Z_-}+L_{Z_+}+L_{Z_-}L_{Z_+}\). Here \(H_P\) factors exactly into the short coprime squarefree harmonic sum times \(\prod_{p\mid210}(1+1/p)\).

For the remaining prime weight, put \(f(x)=x^{-s}/\log^2(Nx)\). Chebyshev's elementary bound \(\psi(x)\le3x\) holds for \(x\ge1\). Indeed, at powers of two, each difference \(\psi(2n)-\psi(n)\) is bounded by \(\log\binom{2n}{n}\le2n\log2\) (each prime power in the interval contributes through its prime to the binomial valuation). Bounding \(x\) by the next power of two yields \(\psi(x)\le4x\log2<3x\). Partial summation and \(f'\le0\) give
\[
 \sum_{m\le M}\Lambda(m) f(m)
 \le3\left[f(1)+\int_1^M f(x)\,dx\right].
\]
The integral is bounded by 64 equal logarithmic intervals: hold the denominator at each left endpoint and integrate \(x^{-s}\) exactly. Multiply by the mass of \(F\) and divide by \(\pi\Delta R\) to get the table. At \(\eta\ge s\), the same mass estimates apply. This allows subtraction of the forward Dirichlet spectrum even through \(T^4\) at explicitly small cost. The contribution correlated with ordinates of rightward zeros still requires estimation.

To reproduce the last row use **python -B quadratic_contour.py --spread 2.5 --prime-power 4**.
