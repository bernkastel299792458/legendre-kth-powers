# Two logarithmic tapers with a shared head

Fix \(Y=hT,\ 0<W_0<W_1,\ 0\le\theta\le1\). Let \(\lambda_0=1-\theta,\ \lambda_1=\theta\), and let \(\omega_i\) be one through \(Y\), linear in \(\log n\) from \(Y\) to \(Ye^{W_i}\), and zero thereafter. In the Euler detector use \(\omega=\lambda_0\omega_0+\lambda_1\omega_1\). For \(\log T\ge U,\ e=2\delta/\log T,\ e_0=2\delta/U\le .1,\ \log Y_0=U+\log h>16\), the [program](mixed_low.py) returns one uniform upper bound per closed \(e\)-cell for
\[
 \frac{S_Q(1+e)}{Y^{-e}\log T}.
\]
The factors \(Y^{-e}\), \(\log T\), and the cell-specific estimate of \(\zeta_Q(1+e)/\log T\) are exactly those of the [single-taper Mellin proof](../../round4/density/MELLIN_LOW.md). The finite Euler-factor set, Möbius-sum constants, reciprocal-zeta bound, and Euler–Maclaurin remainder have the same hypotheses.

**Continuous norm.** In the notation of that proof write \(B(u)=\lambda_0 B_{W_0}(u)+\lambda_1B_{W_1}(u)\) and put
\[
 C(z)=\sum_{i=0}^1 \frac{\lambda_i}{W_i}(1-e^{-W_i z}),\qquad
 c=\frac{\lambda_0}{W_0}+\frac{\lambda_1}{W_1}.
\]
Linearity of the centered logarithmic weight and Fourier–Plancherel give, at \(z=e/2+it\),
\[
 I_e=\frac1\pi\int_0^\infty\frac{|C(z)|^2}{|z|^4|\zeta_Q(1+z)|^2}\,dt.
\]
The two complex exponential differences share the same origin \(\log Y\); the code adds them before taking the absolute value. On \(0\le t\le1/4\) it evaluates \(z\zeta(1+z)\) via the original Euler–Maclaurin bound and caps the remaining numerator by
\[
 \left|\frac{C(z)}z\right|
 =\left|\sum_i\lambda_i\int_0^1 e^{-W_i z s}\,ds\right|\le1 .
\]
Whenever the rectangle has a positive lower bound on \(|z|\), the upper bound on \(|C(z)|\) divided by that lower bound is also available. Above height 100, \(|C(z)|\le2c\), so in the tail estimate \(1/W\) becomes \(c\). All division by a modulus lower bound is preceded by a positivity check. The Fourier identity is needed only for \(e>0\); the first cell uses the limiting analytic majorant at \(e=0\).

**Small divisor indices.** Let \(S=(3/5)\log Y_0\), \(s=\log(Y/j)\ge S\), and denote the earlier single-residual bound by
\[
 |R(s)|\le e^{-es}\left\{\frac{A}{s}+(H_0+H_1s)e^{-s/2}\right\}.
\]
The mixed expression at \(-s\) is \(cR(s)-\sum_i(\lambda_i/W_i)R(s+W_i)\). Thus
\[
 |B(-s)|\le e^{-es}\left\{\frac{2Ac}{s}+(C_0+C_1s)e^{-s/2}\right\},
\]
where, writing \(d_i=e^{-W_i/2}\),
\[
 C_0=\sum_i\frac{\lambda_i}{W_i}\{H_0(1+d_i)+H_1W_i d_i\},\qquad
 C_1=H_1\sum_i\frac{\lambda_i}{W_i}(1+d_i).
\]
The original discrete comparisons and Minkowski give the head contribution
\[
 \left[2Ac\sqrt{1/S+1/\log^2Y_0}
 +e^{-S/2}\sqrt{(C_0+C_1 S)^2+2C_1(C_0+C_1S)+2C_1^2}\right]^2.
\]

**Remaining indices.** The uniform \(B_0=1+2/\eta,\ \eta=\varphi(Q)/Q\) bound survives convex averaging. The single-width derivative bound \(1+1/W_i\) gives \(|B'|\le1+c\). In the large-index discrete transfer the resulting error is at most
\[
 2^{\omega_0(Q)}\{B_0^2+2B_0(1+c)\}
 Y_0^{e_0-(2/5)(1+e_0)} .
\]
Multiplying the sum of this error, the head, and \(\eta I_e\) by the earlier pole factor proves the stated row bound. The endpoint values \(\theta=0,1\) call the corresponding single-width certificate directly.

For \(U=41,\delta=.92,\log h=-3.5,Q=210,\ W_0=8.5,W_1=12,\theta=.3\), the first and last of sixteen bounds are below \(.045894141261,.039376258654\). For comparison, the corresponding single width \((1-\theta)W_0+\theta W_1=9.55\) gives bounds below \(.046986052300,.040011346613\). On each of these sixteen cells the ratio of the mixed bound to the separate Minkowski estimate \((\lambda_0\sqrt{D_{0}}+\lambda_1\sqrt{D_{1}})^2\) is below \(.973552\), with \(D_i\) the certified single-width cell values. These numbers concern the low norm. A fourth-power budget must also use the critical-line and high-norm estimates belonging to the same mixed detector.

~~~sh
python -B mixed_low.py --compare
~~~

**Sharper discrete transfer.** Optional \(\texttt{tight=True}\) also applies to a single width by setting \(\theta=0\) or \(1\). For the ordered units \(r_j\) in \(1,\ldots,Q\), indexed from \(j=0\), the maximum oscillation of the periodic count error \(A(x)-\eta x\) is
\[
 D_Q=\max_j(j+1-\eta r_j)-\min_j(j-\eta r_j).
\]
Indeed its slope is \(-\eta\) between jumps, and the two limits at each jump are the quantities in this formula. Every half-open interval therefore has count discrepancy at most \(D_Q\). For \(Q=210\) this is \(106/35\).

For any \(0<\alpha<1\), the same partial summation on \(j>Y^\alpha\) gives \(D_Q\{B_0^2+2B_0(1+c)\}Y_0^{e_0-\alpha(1+e_0)}\), when the exponent is negative. On the remaining indices substitute \(S=(1-\alpha)\log Y_0>\log15\) into the displayed head bound. The function \(1/[j\log^2(Y/j)]\) decreases there since \(S>2\), and the square-exponential comparison remains the same integral from \(S\) to infinity. Each complete pair of head and discrepancy bounds is uniform at all heights \(T\ge e^U\). The program takes the minimum of these complete pairs over \(\alpha=j/100,\ 32\le j\le75\), retaining only admissible choices.

At the sixteen-cell example above the first and last bounds improve further to \(.045701571234,.039162602174\). At \(U=30\) and with four cells, for the same other parameters, the original splitting gives \(.065230421,.060460491\) on the first and last cells. The sharper transfer gives \(.049594946,.042982875\).

~~~sh
python -B mixed_low.py --tight
python -B mixed_low.py --U 30 --cells 4 --tight
~~~

2026-11-20. Joint project AI authors are Claude and Codex. Codex derived and checked the shared-head Mellin and discrete bounds.
