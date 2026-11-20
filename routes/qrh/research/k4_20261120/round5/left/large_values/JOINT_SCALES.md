# Joint signed cutoffs at one zero

Use the notation and hypotheses of [GAUSSIAN.md](GAUSSIAN.md), with the original \(Q=210,N=32768\) polynomial, \(D=3/8,\ b=\sqrt2D,\ s>.5,\ d=\beta-.5\), and \(Y=c_YT\). For each \(\ell=-4,-3,\ldots,4\) define
\[
 X_\ell(\rho)=e^{d\ell}\bigl(1+D_{Ye^\ell}(\rho)\bigr),
 \qquad G_{ij}=\exp(-b^2(i-j)^2/4).
\]
The matrix \(G\) is positive definite, since it is the Gram matrix of the distinct exponentials \(e^{ijv}\) for the Gaussian probability measure \(e^{-v^2/b^2}dv/(\sqrt\pi b)\).

**Joint estimate.** For every node of the complete finite height box, and counting multiplicities, the number of zeros \(\beta>s,\ H<\gamma\le T\) with \(X^*G^{-1}X\ge.35^2\) is less than \(.135161R_s\) for \(c_Y=128\), or \(.052786R_s\) for \(c_Y=512\), where \(R_s=7(\log T)T^{p_s}\) is the original finite-box target. For a target normalized with 6, the corresponding fractions must be multiplied by \(7/6\).

For the proof, let \(U_\ell=e^{d\ell}I_{\rho,\mathrm{near}}(Ye^\ell)\), where the integration is restricted to \(|v|\le40\). The common factor \(Y^{-d}\) can be taken outside every \(U_\ell\), leaving the same integral kernel multiplied by \(e^{i\ell v}\). With \(a=c-\beta,\ \tilde a=c-(1-\beta),\ c=2s-1/2\), use the weight \(P=P_a+P_{\tilde a}\) of [RIESZ.md](RIESZ.md). The weighted Cauchy–Schwarz estimate for any complex scalars \(u_j\) gives
\[
 \left|\sum_j\overline{u_j}U_j\right|^2
 \le Y^{-2d}\int_{-40}^{40} P(v)|(\zeta P_{\rm moll})(1/2+i(\gamma+v))|^2\,dv
 \quad \times\!\!\int_{-40}^{40}\frac{|K(-d+iv)|^2}{4\pi^2P(v)}
          \left|\sum_j\overline{u_j}e^{ijv}\right|^2\,dv .
\]
Here \(K(w)=e^{w^2/(2b^2)}/w\) and \(P_{\rm moll}\) denotes the polynomial, to distinguish it from the Poisson weight. The second integral is at most \(J_s^{\rm pair}\, u^*G u\), with
\[
 J_s^{\rm pair}=\frac{e^{D^2/b^2}\sqrt\pi\,b}{4\pi^2}
                 \frac{3}{2(c-\tfrac12)}.
\]
Indeed the pointwise Cauchy-kernel factor is bounded by that constant times \(e^{-v^2/b^2}/(\sqrt{\pi}b)\). It is then legitimate to extend the last integral to the entire real axis even for complex coefficients since the integrand is nonnegative. Fourier transformation gives the stated Gram matrix. Choosing \(u=G^{-1}U\) (or the zero vector when \(U=0\)) supplies the ellipsoidal bound with the same right side as the one-point Cauchy inequality. No sum of independent count budgets is involved.

The difference between \(U_j\) and \(X_j\) arises from the horizontal tails, the residue at 1, and \(1-\Phi(b\log(Ye^j))\). The proof of GAUSSIAN.md bounds the first two below \(10^{-40}\) even at the extreme scales: \(Y e^{-4}>1\) and \(\log Y+4<56\). At the smallest scale \(Y e^{-4}\ge128 H e^{-4}\), the script checks \(1-\Phi<10^{-40}\). The error in the \(G^{-1}\)-norm is less than
\[
 e^{4D}10^{-39}\left(\sum_{i,j}|(G^{-1})_{ij}|\right)^{1/2}<10^{-30};
\]
the factor in parentheses after its square root is below 3959. Sum the one-point integral in the first display over the zeros, exactly as in GAUSSIAN.md, and replace the threshold by \(.35-10^{-30}\). The same \(1/8\)-height grid gives the two fractions quoted above.

Since \(G_{\ell\ell}=1\), every zero outside the one exceptional set satisfies \(\Re D_{Ye^\ell}(\rho)<-1+.35e^{-d\ell}\) at all nine lengths. For \(s=.85\), the simultaneous signed upper bounds at \(\ell=-2,-1,0,1,2\) are respectively \(-.25904,-.49075,-.65,-.75335,-.82619\). The non-diagonal part also constrains differences. For example taking the two-dimensional principal Gram matrix at \(\ell=0,1\) gives
\[
 |X_0|^2+\frac{|X_1-gX_0|^2}{1-g^2}<.35^2,\qquad g=e^{-b^2/4}.
\]
A large deviation at one cutoff therefore reduces the allowance for the orthogonal combination of the next cutoff.

The same dual argument with test functions \(1,iv\) has diagonal Gram entries \(1,b^2/2\) and vanishing off-diagonal entry. For the truncated critical integrals it gives
\[
 |I_{\rho,\mathrm{near}}(Y)|^2+\frac{2}{b^2}
 \left|\left(\partial_{\log Y}+d\right)I_{\rho,\mathrm{near}}(Y)\right|^2
 \ \le J_s^{\rm pair}Y^{-2d}\int_{-40}^{40}P(v)|\zeta P_{\rm moll}|^2\,dv .
\]
The derivative in the physical coefficients is a Gaussian band weight. This formula records the direct signed linkage between the cumulative tail and a localized derivative without an extra Type II cost. The numerical nine-point theorem above uses the finite Gram matrix, independently of this derivative variant.

With \(Y=512T\) it remains sufficient, for instance, to prove that the number of zeros satisfying the displayed *small-ellipsoid* condition is at most \(6.63(\log T)T^{p_s}\) throughout the box. This number is still unknown. Merely verifying how often the corresponding Dirichlet sums are large at generic ordinates would not prove it.

Run **python -B joint_scales.py**. The kernel estimate, finite comparisons, and their limitations were derived by Codex under the workspace's joint Claude/Codex attribution protocol.
