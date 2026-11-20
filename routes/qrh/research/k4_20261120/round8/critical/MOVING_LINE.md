# Moving the Gabriel left boundary

**Connected upper half-line at $L=143$.** Allowing the three left boundaries $1/2-.004,1/2-.008,1/2-.012$ along with $1/2$ gives a maximum physical budget below $.999529050$ on the entire closed interval $[143,143.45]$. Its right endpoint overlaps the $143.434$ certificate below. Under the same QRH$(7/8)$ and finite-height inputs this covers all integers $n\ge3\,357\,590\,504\,895\,459$. The following command, run from the research directory, regenerates the [sixteenth-height table](shift_rows_16.json) and recomputes every ordinate and physical estimate. The verifier checks equality if the table exists. The two computations use the same seven full detector parameter triples.

~~~powershell
$env:OPENBLAS_NUM_THREADS='1'
python -B round8/critical/shift_parallel.py --first 143.0 --last 143.45 --join 143.434 --sub 16 --nh 28 --mesh 192 --cutoff 320 --workers 4 --shifts .004,.008,.012 --export round8/critical/shift_rows_16.json
~~~

**Connected upper half-line at $L=143.434$.** The left line $\Re s=.495$ below and the original critical line may be chosen independently for each hinge and detector. For each sixteenth-unit log-height slab in $34\le u<42$ both use the same uniform fourth cap from the [balanced and endpoint families](../../round7/spatial/PROFILE.md). The computations at other heights and on the other three sides use the previous estimates. The [parallel verifier](shift_parallel.py) prices the full polygon including all real-part knots, the infinite ordinate tail and prime powers, with the same upward integer rounding of all boundary constants. On $[143.35,143.88]$ its consecutive suffix from the right contains $[143.434,143.88]$, with budget below $.999860718$. The full interval maximum exceeds $1.00235$ at $143.35$. Joining to [the earlier $143.874$ half-line](../../round7/spatial/PROFILE.md) covers all integers $n\ge3\,742\,386\,857\,618\,206$ under QRH$(7/8)$ and the earlier finite-height inputs.

~~~powershell
python -B round8/critical/shift_parallel.py --first 143.35 --last 143.88 --join 143.434 --workers 4
~~~


We retain the same tapered residual $f_{2310}$, the original right endpoint of order two, and the left endpoint of order $4/3$. Put $R=1+\delta/u$, $L_0=1/2$, and $\theta=(R-s)/(R-L)$, where $s$ is the desired real-part hinge. In terms of the unnormalized endpoint integral upper bounds $A,B$, the logarithm of the cost supplied by Gabriel's theorem is
\[
 \log j(\nu)+\nu\log N+P\log A+(1-P)\log B,\qquad
 \nu=4/(2+\theta),\quad P=3\theta/(2+\theta).
\]
Here $j$ is the [certified angular factor](../../round6/reduction/exact_bridge.py) and $N=(1+10^{-6})^2/(1-1/(3\cdot10^{12}))$. Holding $u,R,s$ fixed, moving the left line rightward improves this cost to first order precisely when
\[
 -(\log A)'>{2\over(2+\theta)(R-L)}
    \left[\log(A/B)-\tfrac23\{(\log j)'(\nu)+\log N\}\right].
\]
At ties one takes the appropriate one-sided active slope. For a nonzero displacement the verifier isolates $\log A(L+h)$ directly in the displayed cost. It uses all exact active chords for the differential test, independently of any floating-point derivative.

With $\delta=1.1,\ W=9.5,\ \log h_{\rm taper}=-3$ and cutoff 100, the required slopes for the certified finite-row endpoint norm at $u=35,37,40$ are respectively $66.860922,\ 70.341858,\ 75.580030$ at $s=.84$ (rounded to six decimal places). At $u=37,\ s=.84$ the left integral ratio for right displacements $.005,.01,.02,.04$ must be below $.703484,.494888,.244913,.059983$, respectively (rounded up). These are thresholds relative to the current numerical interpolation certificate at the specified $u$. They are not lower bounds on the unknown true means. The coefficient gap $Y=e^{u-3}$ alone gives rate $(4/3)(u-3)$ in the ideal positive-frequency Hardy space.

## Off-critical fourth moment with vanishing linear correction

Write $Z(s)=\zeta(s)E_q(s)$ for squarefree $q$ having at least one prime factor, and $F(s)=Z(s)Z(1-s)$. The zero of $E_q(0)$ cancels the pole at each of 0 and 1 in $F$, so $F$ is entire. Also $F(1-s)=F(s)$ and $F(1/2+it)=|Z(1/2+it)|^2$. For $T=e^u$, $D=1.01T$, $K=2^{32}$ and $p\in[2047,2048]$, multiply by the holomorphic branch
\[
 w(s)=\{1+[(s-1/2)/(iD)]^K\}^{-p/(2K)} .
\]
Within $|\Re s-1/2|\le1.5$ the bracket has no zero for $u\ge34$. At $|t|\ge D/2$ its added complex power has argument modulo $2\pi$ at most $3K/D<\pi/2$, and hence the modulus of the bracket lies between $\max(1,(|t|/D)^K)$ and $2\max(1,(|t|/D)^K)(1+9/D^2)^{K/2}$. At smaller heights the added term is at most $.51^K$. Consequently
\[
 (1-10^{-6})G_p(t)\le |w(\sigma+it)|^2\le(1+10^{-9})G_p(t),
 \qquad G_p(t)=\min(1,(D/|t|)^p).
\]
The window has the same reflection symmetry and real coefficients around its midpoint.

Let $B(h)=\int_\mathbb R |wF(1/2+h+it)|^2dt$. Plancherel and horizontal translation of an analytic function give $B(h)=\int\cosh(2h\xi)d\mu(\xi)$ for a finite positive measure. Indeed the critical trace is real, so its squared Fourier modulus is even, and the holomorphic shift multiplies its transform by an exponential; contour shifts are valid here by the high polynomial decay on every line of the compact strip. For $0\le r=h/d\le1$,
\[
 B(h)\le B(0)\cosh\!\left(r\,\operatorname{arcosh}{B(d)\over B(0)}\right).
\]
This is Jensen for $x\mapsto\cosh(r\operatorname{arcosh}x)$, concave on $[1,\infty)$ because $r\tanh t\le\tanh(rt)$. The homogeneous right hand side increases in both coordinates: monotonicity in the first is equivalent to $\tanh t\ge r\tanh(rt)$. Thus certified upper bounds on both edges can be substituted when the selected far upper exceeds the center upper.

Choose $d=1/2+\eta$, $1/8\le\eta\le2/5$. At $1+\eta$ the absolute Euler product gives
\[
 |F(1+\eta+it)|^2\le
 |\chi(-\eta+it)|^2\zeta(1+\eta)^4
 \prod_{l\mid q,\ l\ {\rm prime}}[(1-l^{-1-\eta})(1+l^\eta)]^2 .
\]
For $0<h\le.1$ the functional equation relates the left fourth moment to $|F|^2$ through
\[
 |Z(1/2-h+it)|^4
 \le |F(1/2-h+it)|^2|\chi(1/2-h+it)|^2
 \prod_{l\mid q,\ l\ {\rm prime}}
 [(1+l^{-1/2+h})/(1+l^{-1/2-h})]^2.
\]
The maximal Euler ratio occurs at phase $\pi$, by differentiating its squared ratio in the phase cosine. These bounds remain true at zeros by continuity.

Both gamma bounds used here have the form $|\chi(1/2-v+it)|\le[1.000001\max(10^9,|t|)/(2\pi)]^v$, for $v=h$ or $v=d$. At $|t|\ge1000$, put $y=|t|/2$ and integrate $\Re\psi(x+iy)$ over $(1/2-v)/2\le x\le(1/2+v)/2$. For $x+1>0$ comparison of the Euler sum for $\psi$ with its integral gives $\Re\psi(x+1+iy)\le\frac12\log((x+1)^2+y^2)+2/y$, using the total variation of $a/(a^2+y^2)$ on $[0,\infty)$. The recurrence adds at most $1/y$. This is below $\log(1.000001\max(10^9,|t|)/2)$, considering $|t|\ge10^8$ and $1000\le |t|\le10^8$ separately. For $|t|<1000$ and $v=h$ use the same comparison at $x+1$ with variation at most $2/(x+1)$, and omit the nonpositive recurrence term. For $v=d$, the recurrence and the beta integral bound the gamma quotient by $|-\eta/2+iy|\Gamma((1+\eta)/2)/\Gamma(1-\eta/2)$. The gamma ratio is at most $3$ by log-convexity on $[1/2,1]$ and $\Gamma(x)\ge1$ on that interval. This costs below $1503$, covered by the stated cap.

To convert the recovered integral use $p=2048-2h$, so that $\max(10^9,|t|)^{2h}G_{2048}(t)\le D^{2h}G_p(t)$. For the far moment integrate $t^{2d}G_p(t)$ explicitly and pay $10^{9(1+2d)}$ for the small cap interval. The central moment with weight $G_p$ follows from the established half-line primitive bound by layer cake, with factor $1.01^{1+4/U}p/(p-1-4/U)$. The verifier normalizes by $2Tu^4$. For $U\le u\le V$ the main term in the far cap is largest at $V$ because $2dU>4$; the small cap is bounded at $U$. See [shift_zeta.py](shift_zeta.py).

For $37\le u\le37.5$ the complete displaced fourth positive-height integral, divided by $Tu^4$, is below $.000930884,\ .001191672,\ .002131021$ at $h=.0025,.005,.01$. The corresponding factors against the central certified moment are $1.237508,\ 1.584197,\ 2.832958$ (rounded upwards).

## Positive time correlation

The trace $w(1/2+it)F(1/2+it)$ is nonnegative on the complete real axis. For any $v$, Plancherel applied to its autocorrelation gives $\int\cos(v\xi)d\mu(\xi)\ge0$. Fix $X>0$. For $|\xi|\le X$ the power series of cosh and the chord bound on sine give
\[
 \cosh(2h\xi)-1\le(\cosh(2hX)-1)(\xi/X)^2
 \le(\cosh(2hX)-1)(1-\cos(\pi\xi/X))/2.
\]
For $|\xi|>X$ the ratio $(\cosh(2h\xi)-1)/\cosh(2d\xi)$ decreases as $|\xi|$ grows whenever $2dX>4$ and $h/d<1/5$. In fact the positive numerator logarithmic derivative is $2h\coth(h\xi)\le2h+2/\xi$, below $2d\tanh(2d\xi)$ there. Integrating the first majorant on the entire axis and the second on the tail gives
\[
 B(h)\le a+(\cosh(2hX)-1)\{a/2+b/\cosh(2dX)\},\qquad
 a\ge B(0),\quad b\ge B(d).
\]
The verifier takes the minimum of six valid choices and the unconstrained Jensen bound.

## Displaced residual and short core

In [shift_fold.py](shift_fold.py), write $x=2h$, $r\mid q/210$, $n=rd$. The residual coefficients of the ordinary folded mean acquire square weight $n^x$. In each band of the [finite Gram proof](../../round6/folds/FOLD_MEAN.md), bound this positive multiplier by the maximum possible $n^x$, including the overlap of the local subband. The Taylor bounds remain valid because the coefficients retain the residue-class support and only their magnitudes change. The unweighted part can keep the full weight when the short core of fraction $\tau$ and length $N$ is removed. In the harmonic part first use the known central harmonic bound, subtracting exactly $(2\tau-\tau^2)H_N\sum 1/r$ divided by $V$ inside the near window, as the original proof does. Then add the increment with weight $((rd)^x-1)/d$, with factor $(1-\tau)^2$ in $d\le N$. The far time tail uses the full harmonic bound without subtraction.

The harmonic increment above $N$ is estimated from the elementary count $|\sum_{d\le y,(d,q)=1}\mu^2(d)-\rho y|\le C\sqrt y$, $C=2^{\omega(q)}+2$. The weight $\omega(d)^2((rd)^x-1)/d$ is nonnegative decreasing for $d\ge N$, checked by $(1-x)(rN)^x>1$. Stieltjes integration by parts and the total variation, including both endpoints, give absolute remainder at most
\[
 C N^{-1/2}\big\{2[(rN)^x-1]+(rN)^x/(1-2x)-1\big\}.
\]
Indeed the two boundary errors and the variation simplify to $2\sqrt N v(N)+\frac12\int_N^b v(y)dy/\sqrt y$ for the weight $v$. Integrate the continuous main term exactly over the constant head and linear log taper. All positive terms increase when the upper cutoff scale is evaluated at $T=e^V$; divide by $u\ge U$ for the uniform bound. The exact squarefree coprime head is enumerated in contiguous blocks with ratio at most $1+2^{-8}$; each term $d^{x-1}$ is bounded by the left endpoint power. The uniform rounding allowance on $x$ is included in the cached sum.

For the short piece $f_\tau=\tau\zeta E_q M_N-1$, reuse the full [central second moment](../../round5/left/SHORT.md), including the signed first-moment term. Bound the same squared integral on $\Re s=-1$ and interpolate by analytic $L^2$ convexity with the window $w$ above for $p=2048$. The pole at $1$ lies outside this strip. Direct evaluation gives
\[
 |\chi(-1+it)|^2=t(1+t^2)\coth(\pi t/2)/(2\pi)^3\le((t+1)/(2\pi))^3\quad(t\ge0),
\]
and $|\zeta(2+it)|\le\zeta(2)$. In the remaining polynomial $P=E_q M_N$ on $\Re s=-1$, the squared coefficient sum is at most $\prod_{p\mid q}(1+p^2)\sum_{d\le N}d^2$. The off-diagonal cost over $[0,Z]$ is at most $4qN(1+\log(qN))$ times its squared coefficient sum, since $|\log(a/b)|\ge |a-b|/(qN)$ and $\sum|p_a p_{a+j}|\le\sum |p_a|^2$. The factor $(t+1)^3G_{2048}$ is at most $(1.01T+1)^3 G_{2045}$. Integration and Minkowski with the constant 1 give the upper far moment in [shift_detector.py](shift_detector.py). Both edge integrals are divided by $Tu$ before interpolation. The final $4/3$ bound follows from Hölder, the triangle inequality and minimization over $\tau=0,.01,\ldots,1$.

For $L=1/2-h$ the pole remover in the [original Gabriel proof](../../round2/spectrum/PROOF.md) is replaced by $(z-1)/(z+2h)$. Its modulus is at most one throughout the new strip and at least $1-1/H$ on the target line for $|\Im z|\ge H$: its squared modulus is $1-[(\Re z+2h)^2-(\Re z-1)^2]/|z+2h|^2$, whose deficit is at most $5/H^2$. The flat window retains the original upper bound since the entire strip still has $|\Re z|\le2$. The other three boundary costs are the original ones at the unchanged hinge $s$.

In the representative $37\le u\le37.5$ row with $N=2^{18}$, the ratio of displaced to central certified left constants is below $1.06484440,\ 1.17254001,\ 1.38568882,\ 1.96837651$ at $h=.001,.0025,.005,.01$. At $u=37$ and $h=.005$ the break-even ratios for $s=.80,.84,.87$ exceed $1.39613567,\ 1.42149521,\ 1.43334766$. This gives a strict improvement of the individual Gabriel bounds at those points.

~~~powershell
python -B round8/critical/moving_line.py
python -B round8/critical/shift_zeta.py
python -B round8/critical/shift_detector.py
~~~

2026-11-20. Claude and Codex research workspace. This section was derived and computed by Codex.

## Square mean on the other symmetric edge

One may sharpen the estimate at $1+\eta$ down to $\eta=.018$. The zeta functional equation contributes $|\chi(-\eta+it)|^2$. For $s=1+\eta+it$ the remaining factor is the squared modulus of
\[
 \zeta(s)^2 E_q(s)E_q(1-s)=\mu(q)q^{s-1}\sum_{n\ge1} b_n n^{-s}.
\]
Here $b_{p^j}=j+1$ for $p\nmid q$, and $b_{p^j}=1-p$ for $p\mid q$ and $j\ge1$. Consequently the squared Dirichlet series at real $r>1$ is
\[
 D_r={\zeta(r)^4\over\zeta(2r)}\prod_{p\mid q}
 { [1+p(p-2)p^{-r}](1-p^{-r})^2\over 1+p^{-r}},
\]
and its absolute counterpart at $\sigma=1+\eta$ is $A=\zeta(\sigma)^2\prod_{p\mid q}(1-p^{-\sigma})(1+(p-2)p^{-\sigma})$.

The integral of the ordinary Dirichlet polynomial limit over $[0,Z]$ differs from $Z D_{2\sigma}$ in absolute value by at most
\[
 E=6(1+1/\eta)D_{1+\eta}+2A^2/\log2 .
\]
Indeed a pair with $n>2m$ has reciprocal gap at most $1/\log2$. For $m<n\le2m$ use $1/\log(n/m)\le n/(n-m)$, $2|a_na_m|\le |a_n|^2+|a_m|^2$ and the two orderings. **For the coefficient attached to the *smaller* index $m$ the sum is**
\[
 \sum_{k=1}^m (m+k)/k\le m(2+\log m).
\]
For the larger index $n$, the sum is at most $n(1+\log n)$. Including the oscillatory integral and the two orders gives a bound $2\sum n(3+2\log n)|a_n|^2$. In the verifier a uniform allowance $6(1+1/\eta)D_{1+\eta}$ dominates it, since $n^{-\eta}(1+\log n)\le1+1/\eta$. Absolute convergence permits passage to the limit. The far weight $\max(10^9,t)^{2d}G_p(t)$ has variation at most $2(1.01T)^{2d}$. Thus integration by parts charges the error only twice this scale, and its exact diagonal uses the same integral of the weight as above. This argument also covers $.01\le\eta\le .4$ in the gamma estimate. [NIST functional equation](https://dlmf.nist.gov/25.4.E2) and [digamma series](https://dlmf.nist.gov/5.7.E6).

The equivalent far bounds compete by taking their certified minimum. In the $u=37$ representative check the new displaced left ratio at $h=.005$ is below $1.3812$, and at $h=.01$ it is below $1.943$.

The implementation also retains the main cosine majorant on the tail. For $\xi=X+y$, $y\ge0$, write $A=2hX$ and $c=(\cosh A-1)/2$. The additional numerator is bounded by
\[
 (2hy)e^{2hy}\{\sinh A+2hy\cosh A\}
       +c\pi^2 y^2/(2X^2).
\]
This uses the mean value bound for the difference of coshes and $1-\cos t\le t^2/2$. The positive far denominator is at least $\cosh(2dX)e^{2dy}/(1+e^{-4dX})$. Maximizing $y e^{-ay}$ and $y^2e^{-ay}$ on the half-line gives the terms named `tangent` in [the verifier](shift_zeta.py). Thus the full integrated inequality holds with the smaller of this coefficient and the previous simple tail. The procedure tests ten $X$ choices.
