# A moving zeta detector immediately above the verified height

Assume QRH(7/8) and the analytic inputs documented for the [modulus-210 detector](../../round4/euler/PROOF.md), including finite-height RH. For every real \(x\) with \(115.033663\leq\log x\leq115.033675\), the open interval \((x,x+4x^{3/4})\) has a prime. The proof connects directly to the [previous three rows](PHYSICAL_TAIL.md). Its new ingredient is a short vertical zero-density estimate centered at the height being tested, and its numerical work is in the [192-bit Arb certificate](moving_window.py).

## A moment on a translated short interval

Take \(H=3000175332800\). For each \(D=(50000000+1280000)j/8,\ 1\leq j\leq8\), let \(R=D/2,\ C=H+R,\ U=\log R,\ M=2048,\ v=1.01,\ \bar y=vM/(M-1)\). Freeze all parameters at this \(D\). Use the real-coefficient Dirichlet detector \(f=\zeta E_{210}C_{210}-1\) of the cited paper. Its logarithmic taper has \(Y=Re^{-2.8}\), \(X=e^8Y\). The right line is \(1+\delta/U,\ \delta=.64\). Translate the rational window \(g\) to
\[
 g_C(z)=\bigl(1+((z-iC)/(vR))^M\bigr)^{-1},\qquad
 G_C(t)=\min(1,(vR/|t-C|)^M).
\]
By the [unshifted rational-window proof](../../round2/spectrum/PROOF.md), the three script inequalities with \(R\) show \(|g_C(\sigma+it)|\leq(1+10^{-6})G_C(t)\) uniformly in the strip, and \(|g_C|\geq(1+10^{-6})^{-1}\) for \(|t-C|\leq R\). The pole-cancelling factor remains \((z-1)/z\): it has modulus at most 1 in the strip and at least \(1-1/H\) on the target. Apply [Gabriel interpolation, in CS v2, Lemma 3](https://arxiv.org/html/2507.15184v2#S3) to \(g_C(z)(z-1)f(z)/z\) on its full vertical lines. The poles of \(g_C\) are outside the strip, and its rational decay dominates the at most polynomial growth of \(f\).

All weighted mean estimates below are for *one half the full-axis integral*. The [finite-frequency folded mean](../../round4/hilbert/FOLDED.md) for \(\tfrac12\int_{-J}^J\) holds for arbitrary complex coefficients. Replace each Dirichlet coefficient by its product with \(n^{-iC}\) to bound \(\tfrac12\int_{C-J}^{C+J}\), with exactly the same coefficient norms. The right boundary from the modulus-210 argument therefore works with \(R\) in place of the old height \(T\). The script uses the older signed norm or the direct high norm, whichever is smaller, and the low-variance saving once. The mollifier remaining on the critical line after absorbing \(E_6\) into \(\zeta\) is \(E_{35}C_{210}\). Its support is coprime to 6. The same translation argument applies to its mean square. Its two coefficients use the same harmonic and unweighted sums as in the Euler-factor proof. Denote the bounds by \(K_3U\) on the right and \(C_MR U\) for the remaining critical-line mollifier.

To bound the critical fourth moment, let \(Z(t)=|\zeta(1/2+it)E_6(1/2+it)|^4\), \(B=C+vR,\ p=1+4/\log B\). Write \(C_*= \texttt{fourth_six}(\log B)\). The [sieved Riemann–Siegel fourth moment](../../round4/density/SIEVED.md) gives \(\int_0^z Z(t)\,dt\leq C_* z\log^4 z\) for all \(z\geq B\). For \(u\geq vR\) this bounds \(\tfrac12\int_{C-u}^{C+u}Z(t)\,dt\) by
\[
 \frac{C_* B\log^4 B}{2}
       (u/(vR))^p(1+\mathbf{1}_{u\geq C}).
\]
Indeed \(Z\) is even, \(C+u\leq B u/(vR)\), and \(\log(C+u)/\log B\leq(u/(vR))^{1/\log B}\). Integrating against the probability law with density \(M(vR)^Mu^{-M-1}\) on \(u\geq vR\) shows \(\tfrac12\int G_C Z\leq A_4\), where
\[
 A_4=\frac{C_*B\log^4 B}{2}\frac{M}{M-p}
                    (1+(vR/C)^{M-p}).
\]
Minkowski in \(L^{4/3}\) and Hölder give the half-axis left bound
\[
 A_L=\left[A_4^{1/4}(C_M R U)^{1/2}+(\bar y R)^{3/4}\right]^{4/3}.
\]
Both boundary quantities are half of full-axis upper bounds. Their powers \(P,1-P\) sum to 1. The target integral over \([H,H+D]\) is bounded by the entire integral at the interpolated abscissa; no symmetry about \(C\) is assumed for \(f\). Hence
\[
 \int_H^{H+D}|f(s+it)|^\nu dt
 \leq 2\left(\frac{(1+10^{-6})^2}{1-1/H}\right)^\nu
       A_L^P(K_3U)^{1-P},
 \quad
 P=\frac{3(1-s)+3\delta/U}{2-s+3\delta/U},\quad
 \nu=\frac{2+4\delta/U}{2-s+3\delta/U}.
\]

## Three other sides of the rectangle

Use a fixed \(D_q(w)=(1+w)(1-w/q)^q\), \(3\leq q\leq8\), for each individual rectangle and abscissa. On the right side all coefficients of \(f\) up to \(Y\) vanish and the remainder are bounded in modulus by \(d(n)\). Since \(\sum_{n\leq t}d(n)\leq t(1+\log t)\), partial summation gives
\[
 |f(2+it)|\leq\sum_{n>Y}d(n)n^{-2}
       \leq 2\int_Y^\infty(1+\log u)u^{-2}\,du
       =2(\log Y+2)/Y=:a_2.
\]
The script checks \((1+a_2)^9<3/2\). Therefore the [detector Taylor estimate](../../round2/spectrum/PROOF.md) gives right-side cost \(2a_2^2D/(2\pi)\).

On either horizontal edge at height \(y\), use Jensen on the real part via the holomorphic symmetrization \((D_q(f(z+iy))+D_q(f(z-iy)))/2\). As in the [original Littlewood argument](../../upper/PROOF.md), at the center \(z=2\) its value exceeds \(1/2\). On \(|z-2|\leq1.5\), Euler summation and the finite Dirichlet coefficients show that its modulus is at most \(O^{q+1}\) with \(O=11\sqrt{210X}(H+D+6)\). For \(u>0\), the number of sign-boundaries of the real part on \([2-u,2]\) is at most \((\log 2+(q+1)\log O)/\log(1.5/u)\). This counts zeros with multiplicity and can overcount. A continuous determination of the argument along the horizontal segment thus has absolute value at \(2-u\) at most \(\pi\) times this bound plus \(2\pi\). Subdivide \(0\leq u\leq2-s\) into 16 parts and use the right endpoint of each to integrate the increasing bound. Including both horizontal edges and dividing by \(2\pi\) gives the script's \(2(2-s)\) plus its 16-term Jensen sum. Detector and taper are frozen when taking boundary limits. The upper height approaches \(H+D\) from above, and the lower height can approach \(H\) from below inside the verified-RH range. The horizontal and right-side estimates pass to these limits as explained in the [rectangle proof](../../round2/right/PROOF.md).

At each node and each height, add all costs for the *same* \(q\), including the [radial majorant](../../round2/detector/adaptive.py) for the interpolated side, before minimizing over \(q\). This bounds the sum of horizontal zero distances \(\sum_{H<\gamma\leq H+D}(\beta-s)_+\) under the ordinary Littlewood normalization. Convert this to a bound on \(\sum e^{(\beta-1)l}\) under QRH by the consecutive secant slopes on the actual nodes \(0.650,0.653,\ldots,0.866,0.875\), plus the explicit Riemann–von Mangoldt difference on the zero-order term. The implementation uses \(\texttt{range}(650,869,3)\), ending at 866.

## Transfer to prime intervals

Set \(K=H+50000000\) in the [signed test with its refined exterior prime estimate](PHYSICAL_TAIL.md). Replace the original unverified-zero cost by the [Gaussian spectral envelope and its cumulative-height decomposition](SHORT_BOX.md), using eight equal intervals from \(H\) to \(K+1280000\). The cumulative bounds for the eight right endpoints are exactly those just proved. The Gaussian tail beyond \(K+1280000\) stays below \(10^{-1700}\); the positive and negative ordinate factor is included. All lower and upper endpoints in the geometric and arithmetic estimates are evaluated throughout the whole real \(L\)-slab as in the previous proof. The total normalized cost is below \(0.999999129\). Run the script at 192 bits to check the bound and the integer endpoint.
