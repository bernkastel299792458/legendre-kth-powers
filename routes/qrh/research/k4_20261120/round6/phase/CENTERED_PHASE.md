# Centering the interference term

Use the paired real cutoffs and notation of [the fourth-moment bound](SMOOTH_PHASE.md) and [the mixed moment](MIXED_PRODUCT.md). All expectations below integrate with measure \(dt/T\), and may also average over the cutoff parameter. Both polynomials vanish on \(t<t_0\), with \(t_0\) the common AFE starting point. Include \(Q^{-1/2}\) in the dual polynomial. Write \(S=|A|^2+|B|^2\) and \(V=2\Re(e^{i\phi}AB)\) in the conjugated convention for \(B\); \(S+V\) is the square modulus of the main term. Take \(U\le u=\log T\le U+b\). Suppose

\[
 ES^2\le a u^4,\quad EV^2\le c u^4,\quad ES\ge m\ge0,\quad |EV|\le h.
\]

Applying Cauchy to \((S-m)V\) gives
\[
\frac{E(S+V)^2}{u^4}\le a+c+
 2\sqrt{c\{a-m^2/(U+b)^4\}_+}+2mh/U^4 .
\]
The previously proved estimates give \(a=C_F+C_D+2Z\), \(c=2(Z+H)\). The AFE error and the initial interval are added as in the disjoint bound. For \(u>U+b\) take the existing uniform projected bound starting at \(U+b\).

### Positive mean

For either sharp polynomial let its real coefficients be \(v_j\), omitting the dual scaling for the moment. Its cutoff is \(\sigma\sqrt t\), where \(\sigma\) varies over the paired interval. Put \(Y=(\min\sigma)\sqrt T,\ Z=(\max\sigma)\sqrt T\). For \(j\le Y\) the integration length is at least \(T-t_0-Tj^2/Y^2\). With \(\sum_{n\le x}v_n^2=\rho x+O(D)\) uniformly in real \(x\ge0\), ordinary partial summation gives \(\sum_{j\le Y}jv_j^2\le \rho Y^2/2+2DY\). The periodic digamma calculation in periodic_fourth.harmonic gives
\(\sum_{j\le Y}v_j^2/j\ge \rho\log Y+c_0-2D/Y\).
For the off-diagonal unrestricted absolute sum, each pair has a single time interval with integral of absolute value at most \(2/|\log(n/m)|\). The reciprocal-gap bound gives
\[
 \sum_{m<n\le Z}\frac{1}{\sqrt{mn}\log(n/m)}
 \le Z(1+\log Z)+\sum_{m<n\le Z}(mn)^{-1/2}
 \le Z(3+\log Z).
\]
Including the two orientations, a lower bound for the normalized mean square is
\[
(1-t_0/T)(\rho\log Y+c_0-2D/Y)-\rho/2-2D/Y
-4\max_j|v_j|^2 Z(3+\log Z)/T .
\]
The harmonic lower bound is checked positive at \(u=U\); then the complete right side increases for \(u\ge U\), because \(Z>1\). Sum the forward bound and the dual bound divided by \(Q\) to obtain \(m\).

### Signed mean of the interference

Fix one cutoff \(\alpha_0\in[\alpha e^{-w},\alpha e^w]\). The terminal forward and dual lengths \(X,Y'\) satisfy \(XY'=QT/(2\pi)\) and \(X/Y'=\lambda=\alpha_0^2\). The phase of a pair of indices is, up to a constant or complex conjugation,
\[
  \Phi(t)=t\log(Qt/(2\pi e))-t\log(nj).
\]
On the single active interval, \(\Phi'\ge |\log(n/(\lambda j))|\), since the two lower time thresholds are \(2\pi n^2/(Q\lambda)\) and \(2\pi j^2\lambda/Q\). Monotonicity and one integration by parts bound the integral by \(2/\varepsilon\) if \(|\log(n/(\lambda j))|\ge\varepsilon\). Uniformly it is at most \(3\sqrt T\): integrate length at most \(\sqrt T\) above the stationary point \(t_*=2\pi nj/Q\) trivially, and use \(\Phi'(t)\ge (t-t_*)/t\ge T^{-1/2}\) afterwards.

Take \(\varepsilon=T^{-1/4}<0.1\) and \(M=\max_j|c_Q(j)|\). The absolute contribution of the far ratios to the complex mean, before the real part is doubled, is at most \(8M\varepsilon/\sqrt{2\pi}\). This uses \(\sum_{n\le x}n^{-1/2}\le2\sqrt x\). For each \(j\le Y'\) there are at most \(1+3\varepsilon\lambda j\) remaining \(n\), each satisfying \((nj)^{-1/2}\le e^{\varepsilon/2}/(\sqrt\lambda j)\). Since \(\sqrt\lambda Y'=\sqrt{QT/(2\pi)}\), this part costs at most
\[
 3M e^{\varepsilon/2}
 \left(\frac{3\varepsilon}{\sqrt{2\pi}}+
       \frac{1+\log Y'}{\sqrt{\lambda QT}}\right).
\]
These bounds decrease when \(T\) grows for the parameter range checked in code. Replace \(Y'\) by its maximum over the allowed cutoffs and \(\sqrt\lambda\) by its minimum. Doubling the sum gives \(h\), uniformly over the cutoff average as well.

The uniform entry point is **centered_phase.fourth(U,q,alpha,width,Z,slab)**. Running **python -B centered_phase.py** compares it to the previous projected bound at \(U=37\). All numerical inequalities use Arb.
