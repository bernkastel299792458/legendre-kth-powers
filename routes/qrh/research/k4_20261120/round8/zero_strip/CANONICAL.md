# A detector with exactly the zeta zeros

On the frozen high rectangle put \(f=\zeta M-1\) with the usual squarefree, logarithmically tapered Euler mollifier. The function

\[
 D_0(s)=\zeta(s)\exp[-f(s)]
\]

has exactly the zeta zeros, with their true multiplicities. Its exponential is nonvanishing and the rectangle is disjoint from the pole of zeta. On a vertical line its logarithm obeys

\[
 \log|D_0|=\big(\log|1+f|-\Re f\big)-\log|M|.
\]

The identity holds away from the isolated zeros and extends to the locally integrable logarithms. For \(1<\nu<2\) the sharp radial constant bounding the parenthesis by \(C_\nu |f|^\nu\) follows from a one-variable computation. With \(r=|f|\) and \(x=\Re f\), maximize \(\frac12\log(1+2x+r^2)-x\) on \([-r,r]\). The maximum is \(r^2/2\) for \(r\le2\) and \(r+\log(r-1)\) for \(r\ge2\). On the second range the derivative of the quotient has the sign of

\[
 (1-\nu)r+\frac r{r-1}-\nu\log(r-1).
\]

This decreases strictly from \(4-2\nu>0\) to negative infinity. Thus \(C_\nu\) is the value at its unique root. The [interval calculation](canonical.py) gives \(C_\nu<0.616442\) for the \(s=.85,\log T=36,\ell=.488,\delta=1.1\) hinge. This is a factor below 1.192 times the archived moment constant there. At \(s=.87\) the corresponding factor is below 1.170.

## The unweighted mollifier logarithm

Let \(0<H'<T'\le T\), \(.65\le a<1\) and \(X=Ye^W\). Each coefficient of \(M\) has absolute value at most one, vanishes above \(QX\), and agrees with \(\mu(n)\) for \(n\le Y\). Indeed each squarefree \(n\) has a unique decomposition into its prime factors dividing \(Q\) and a complementary divisor coprime to \(Q\). Its coefficient is precisely \(\mu(n)\) times the taper of that complementary divisor. The difference from \(\mu(n)\) has absolute value at most one even above \(Y\). Hence on \(\sigma=2\),

\[
 |M-1/\zeta|\le\sum_{n>Y}n^{-2}\le1/(Y-1),\qquad
 |\log(\zeta M)|\le2/(Y-3),\quad Y>3 .
\]

The signed integral of \(\log|\zeta(2+it)|\) is bounded in absolute value by \(2\zeta(2)/\log2\), using the absolutely convergent Euler logarithm and the elementary exponential integral. To bound the horizontal arguments of \(M\), note \(\Re M(2+it)\ge2-\zeta(2)>0\). On the disk \(|z-2|\le1.5\), \(|M(z+it)|\le\sum_{n\le QX}n^{-1/2}\le2\sqrt{QX}\). Apply Jensen to the analytic real part after a constant rotation that makes the center value positive. All real argument crossings on \([a,2]\) lie in the smaller disk of radius 1.4. Thus the absolute size of either horizontal argument continued from the right is bounded by \(\pi(N+3/2)\), with

\[
 N=\log\big(2\sqrt{QX}/(2-\zeta(2))\big)/\log(15/14).
\]

Littlewood's lemma for \(M\) has nonnegative zero contribution \(2\pi\sum(\beta_M-a)_+\). These estimates give

\[
 \int_{H'}^{T'}\log|M(a+it)|\,dt\ \ge -2(2-a)\pi(N+3/2)-2\zeta(2)/\log2-2T/(Y-3).
\]

Generic boundary limits give the same lower bound if a horizontal passes through a mollifier zero. For \(Q=2310,T=e^{36},Y=e^{33},X=e^{42}\) the lower bound at \(a=.85\) exceeds \(-2841.705\). It does not require QRH.

## The horizontal argument for a bounded test

At any target height above \(3\cdot10^{12}\) and below the frozen height, control \(\arg D_0=\arg\zeta-\Im f\) directly. Put \(c=.98,e=1.05,R=1+\delta/\log T,\theta_s=(R-s)/(R-\ell)\). The normalized strip Poisson kernels in [the two-source proof](WEIGHTED_GREEN.md) have respective suprema \(\cot(\pi(s-\ell)/(2(R-\ell)))/(2(R-\ell)\theta_s)\) and the reflection of this expression. On \(a\le s\le c\) these are bounded by \(P_L=1/[\pi\theta_c(a-\ell)]\) and \(P_R=1/[\pi(1-\theta_a)(R-c)]\), by \(\cot v\le1/v\). The full-line endpoint masses are \(2A_L,2A_R\) by conjugation symmetry. The pointwise interpolation inequality gives

\[
 |f(s+it)|\le N(2P_L A_L)^{3\theta_s/4}(2P_R A_R)^{(1-\theta_s)/2}.
\]

The right-hand logarithm is affine in \(s\), so its integral is elementary. For \(c\le s\le e\) use Euler summation for zeta at \(\lceil T+2\rceil\), with the absolute first remainder at most \(|s+it|\lceil T+2\rceil^{-s}/s\); its finite sum is bounded by \((1+\log(T+4))(T+4)^{1-c}\). The mollifier is bounded by \((1+\log(QX))(QX)^{1-c}\). For \(e\le s\le2\) the simple bound \(1+(1+1/(s-1))^2\) majorizes \(|f|\). Finally apply the preceding Jensen argument to zeta itself, whose center real part is at least \(2-\zeta(2)\) and whose radius-1.5 disk supremum is at most \((T+4)^{1/2}(6+\log(T+4))+1\) by Euler summation. These computations in [canonical_horizontal.py](canonical_horizontal.py) prove \(\int_{.85}^2|f(s+it)|\,ds<1980.449\) and \(\int_{.85}^2|\arg D_0(s+it)|\,ds<3178.389\) on the archived \(U=36,\ell=.488,\delta=1.1,W=9.5,\log h=-3\) row. Thus a bounded nonnegative Green test can charge this latter amount times its uniform horizontal derivative bound per edge.

## Remaining costs

These estimates do not bound \(-\int(1+\eta\cos\omega t)\log|M(a+it)|dt\) for arbitrary source amplitudes, nor the oscillatory right edge of \(D_0\) for a test growing rapidly past \(7/8\). The fixed-height horizontal estimate above also multiplies the actual derivative bound of that test. A globally nonnegative Green test allows a joint lower bound for all of its \(M\)-logarithm sources by applying Green's identity to \(M\) itself. Its extra zeros have nonnegative mass in that case. A signed continuation outside QRH would need control of the negative mass on the actual mollifier zeros or a separate signed right-edge estimate. The latter contains Dirichlet frequencies \(\log(p^j)\) near the physical frequency and is not supplied by the unweighted mean. No new physical interval count in this work uses this detector.

2026-11-20. Joint project attribution to Claude and Codex.
