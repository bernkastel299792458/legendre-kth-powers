# Actual negative stationary integrals on the three-quarter line

Fix the parameters of [the ordered interference](QUARTER_FAR_PAIRS.md), $q=2310,T=e^{37},\sigma=3/4,a=1/2,\alpha_0=64,w=.75$. The [verifier](quarter_negative.py) gives a negative upper bound below $-2.4003390\,10^{10}$ for the **complete** triangle $1\le e<d\le1024$ of actual mollifier indices. This includes all positive and negative coefficients, all raw AFE indices and both conjugates. The 163 terms with $e=1,d\le1000,(d,q)=1,\mu(d)=-1$ have upper bound $-2.8525781\,10^{10}$. The $d=13,e=1$ upper is below $-1.9940024\,10^9$.

## Weighted saddle with complete endpoint control

The complete row $e=1,\ 2\le d\le10000$, with both signs included, has upper bound $-2.8152907\,10^{10}$. When this row is removed first, the $4T$ forward and $32T$ reflected prefix bounds together with the ratio and ordered estimates leave a sufficient positive signed allowance exceeding $3.7599\,10^{10}$ on the unpriced near pairs. This row and the triangle overlap and supply alternative decompositions.

Write $d/e=r/s$ in lowest terms, $R=r/s>1$. For each pair of raw indices $u,j$ the phase, up to conjugation, is $t\log(t/t_0)-t-\pi/4$, $t_0=2\pi Ruj/q$. In $x=\log(t/t_0)$ put $B(x)=V_z(t)F(x)$, $z=a/2$, where $V_z=V(t)(t/t_s)^{-z}$ and $F$ is the probability of the two cutoffs. Here $V$ is extended to its full definition on $0<t<\infty$. Thus $B(0)$ is its value at the stationary time.

Set $S=2P(K/t_s)^{-z}+z+(m+z)(D/t_s)^{-z}$ where $D=1.01T$, $m=2048$, $P=128$. Each of the three pieces of the log derivative of $V_z$ is monotone, and its absolute maximum is charged in $S$. Their combined variation is at most $2S$. The derivative $F'_x$ is bounded by $1/(2w)$, with variation at most $1/w$ from its single activation and subsequent decrease. Thus $\operatorname{Var}B'\le3S+2/w$. The continuous piecewise smooth $B$ is absolutely continuous. The identity $(B(x)-B(0))/x=\int_0^1 B'(vx)\,dv$ shows that the total variation of this quotient is at most that of $B'$. One integration by parts against the true phase, whose derivative is $x$, bounds the absolute error of replacing $B(x)$ by $B(0)$ by $3S+2/w$. The quotient tends to zero at both infinities, and an admissible one-sided representative includes any jump at zero. For the constant amplitude the [Fresnel estimate](RATIONAL.md) on $[t_0/2,3t_0/2]$ and the exterior first derivative bounds $2/\log2,2/\log(3/2)$ give absolute error below $4001$ on $(0,\infty)$. The signed principal term is $B(0)\sqrt{2\pi t_0}e^{-it_0}$, including the AFE phase $e^{-i\pi/4}$.

Initially restrict to $u\le y_{\max},j\le y'_{\max}$ using $t=2T$ for both raw cutoff maxima. Extending the time integration from $[t_s,2T]$ adds at most $(t_s/K)^{2P}t_s/(2P-z+1)+(D/(2T))^m2T/(m-1)$. Removing saddle terms with $t_0$ outside this interval costs at most $\sqrt{2\pi}[(t_s/K)^{2P}\sqrt{t_s}+(D/(2T))^m\sqrt{2T}]$. The retained principal sum may run over every positive $u,j$ since $F(0)>0$ and $t_s\le t_0\le2T$ force both original raw bounds. Multiply these per-atom errors by two for the conjugates, $(de)^{-\sigma}$ and the product of the raw absolute masses computed in [the far-pairs proof](QUARTER_FAR_PAIRS.md), without its mollifier masses.

## The residue calculation

After combining $\sqrt{2\pi t_0}$ with the actual amplitudes the principal sum has prefactor $(4\pi/q)R^{1-\sigma}(de)^{-\sigma}w_dw_e$ and atoms
\[
 u^{-a}\mathbf1_{(u,q)=1}c_q(j)e^{-2\pi i ruj/(qs)}
 V(t_0)\mathbf1_{t_s\le t_0\le2T}F(0).
\]
For fixed unit $u$ the $j$-sequence has period $qs$ and mean $\mathbf1_{s\mid u}$. Expand $c_q(j)=\sum_{h\in(\mathbb Z/q)^\times}e^{2\pi ihj/q}$: the constant requires $hs=ru\bmod qs$, which has exactly one unit solution if $s\mid u$. On any interval of real endpoints replacing the $j$-sum by its mean times length costs at most $qs(\overline{|c_q|}+1)$. For fixed $\alpha$ and a fixed level of the unimodal $V$, the remaining $j$-set is one interval. Average the bound over cutoffs and level sets.

Alternatively put $P_1=qs$. Add one for integer count minus length in the constant mode, and sum $1/|\sin(\pi(hs-ru)/P_1)|$ over nonconstant $h$. Over one period of $u$ its mean is at most $M=1+\varphi(q)(1+\log P_1)$ and its pointwise bound is $A=1+P_1(1+\log P_1)$. Indeed $\sum_{k=1}^{P_1-1}1/\sin(\pi k/P_1)\le P_1(1+\log P_1)$ and $(r,P_1)=1$. These majorants still hold with the unit restriction on $u$. The partial sum through $x$ is at most $Mx+\min(Ax,P_1 M)$ by the pointwise bound and full periods plus one positive incomplete period. Partial summation gives $My_{\max}^{1-a}/(1-a)+A^a(P_1M)^{1-a}/(1-a)$. Take the smaller of this and the first uniform estimate weighted by the unit power sum.

The remaining $u$ are unit multiples of $s$, of density $\eta/s$. For each level of $V$ the inner interval length times $u^{-a}$ has the form
\[
 u^{-a}[\min(Ru/\lambda,B/u)-\max(u/(\lambda R),A'/u)]_+,
 \quad \lambda=\alpha^2,\quad 0\le A'<B.
\]
This quantity is unimodal: below the switch of its upper term the active difference increases with either lower term; above that switch it decreases with either lower term. Its maximum is at most $(R/\lambda)^a(y'_{\max})^{1-a}$. Apply the unit interval discrepancy after scaling the interval by $1/s$, which gives the remaining arithmetic error.

Finally at fixed $t=t_0$ the two raw supports give $(e/d)y\le u\le y$, $y=\alpha\sqrt{qt/(2\pi)}$, and $dj=qe\,dt/(2\pi d u)$. Therefore the continuous signed contribution of this pair equals
\[
 \frac{2\eta}{a}\frac{w_dw_e}{[d,e]}
       (e^{-a}-d^{-a})\int_{t_s}^{2T}V(t)\,\mathbb E_\alpha[y^{-a}]\,dt .
\]
Here $e^{-a}$ means the stated mollifier index $e$ raised to power $-a$. Bound the time integral below by $K\le t\le D$, and above by extending to all positive heights with $G$. For a signed upper bound use the lower integral with negative coefficients and the upper with positive coefficients. Add both absolute errors from every pair. The complete triangle bounds are below $-1.2385\,10^{10}$, $-1.6546\,10^{10}$, $-1.9925\,10^{10}$, $-2.2582\,10^{10}$ and $-2.4003\,10^{10}$ for cutoffs $64,128,256,512,1024$ respectively.

These negative estimates combine with the previous ordered bounds by removing the selected complete pairs before applying the absolute nonstationary estimates to other pairs. [The whole upper half-line](MOVING_LINE.md) does not use these single-height calculations. The higher products and the other stationary terms remain open.

~~~powershell
python -B round8/critical/quarter_negative.py
~~~

2026-11-20. Joint Claude and Codex research workspace.

## Sharper scalar remainder

The final verifier bounds the scalar Fresnel error on $(0,\infty)$ by $18$ and prices the variable-amplitude error by $2S+2/w$. Indeed split
\[
 (B(x)-B(0))/x=V_z(x)(F(x)-F(0))/x+F(0)(V_z(x)-V_z(0))/x
\]
with the shorthand $V_z(x)=V_z(t_0e^x)$. The first divided difference is bounded by $1/(2w)$ and has variation at most $1/w$; multiplication by $V_z$ costs at most a further $1/w$. The second divided difference costs at most $2S$ by the total variation of $V_z'$.

For the scalar bound use $x=t/t_0$, $v=\operatorname{sgn}(x-1)\sqrt{2(x\log x-x+1)}$, $A=dx/dv=h/g$, exactly as in [the prior saddle proof](RATIONAL.md). The [short interval verifier](quarter_fresnel.py) encloses $\sup_{1/2\le x\le3/2}|dA/dv|<.498$ and $\sup |d^2A/dv^2|<.705$. It evaluates the integral formulas $g=\int_0^1(1+s(x-1))^{-1}ds$ and $h^2=2\int_0^1(1-s)(1+s(x-1))^{-1}ds$, together with their first two derivatives by interval Riemann sums for $32$ closed $x$-boxes and $64$ integration bins. The derivatives with respect to $v$ are $AA_x$ and $A^2 A_{xx}+A A_x^2$. The smooth difference $(A(v)-1)/v$ has supremum at most $\sup|A_v|$ and derivative bounded by $\sup|A_{vv}|/2$. Put $l=-v(1/2)$ and $r=v(3/2)$. Summing its integration-by-parts error, the two Fresnel tails and the two original tails gives
\[
 2\sup|A_v|+(l+r)\sup|A_{vv}|/2+2/l+2/r+2/\log2+2/\log(3/2)<17.083 .
\]
The [reduced numerical cost](quarter_negative.py) yields a genuine upper below $-2.9639155\,10^{10}$ for **the complete row $e=1,\ 2\le d\le10000$**, and below $-2.5878154\,10^{10}$ for the complete triangle $e<d\le1024$. With the row removed, the remaining physical near-diagonal and stationary budget from the $4T/32T$ calculation now exceeds $3.90853\,10^{10}$.

~~~powershell
python -B round8/critical/quarter_fresnel.py
python -B round8/critical/quarter_negative.py
~~~
