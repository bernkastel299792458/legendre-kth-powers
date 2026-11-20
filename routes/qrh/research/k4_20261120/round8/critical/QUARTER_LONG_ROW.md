# Genuine cancellation in the entire first mollifier row

Fix $q=2310,T=e^{37}$, $\sigma=3/4$, $a=1/2$, $\alpha_0=64,w=.75$, with the real weight and the true averaged AFE of [the finite stationary triangle](QUARTER_NEGATIVE.md). Over **all** $2\le d\le X=e^{43.5}$ and $e=1$, the true two-conjugate cross term is less than $-1.8790977\,10^{10}$. The calculation covers every raw AFE index, temporal endpoint, and both signs of $\mu(d)$. This is a statement at the representative ordinate, with the cross term integrated over $[t_s,2T]$.

## The finite row and the tail in time

Put $D_0=10^5$, $\epsilon=.03$ and $N_t=qt/(2\pi)$. On the first $d\le D_0$ use [the true negative-pair proof](QUARTER_NEGATIVE.md). All these coefficients have untapered numerator $\mu(d)$. Their continuous main has common time factor and signed scalar $\sum_{1<d\le D_0,(d,q)=1}\mu(d)(1-d^{-a})/d$. Use the matching lower or upper bound for the common factor according to this summed sign. Summation of the elementary time and lattice errors gives the true first partial row upper $-2.80725727\,10^{10}$.

For $d>D_0$, keep the previously defined inner part $\psi(x)=1-R(x)$, with $x=\log(t/t_0)$, $t_0=2\pi duj/q$. It equals one at zero and vanishes outside $|x|<2\epsilon$. Only $uj\le C/d$, $C=N_{2T}e^{2\epsilon}$, can contribute in the integration window. The probability of the simultaneous sharp raw cutoffs, $F(x)$, is replaced by $F(x)\psi(x)$. Its derivative has norm at most $1/(2w)+1/\epsilon$ and variation at most $2/w+5/\epsilon$, by the product rule, $\operatorname{Var} F\le1$, $\operatorname{Var}\psi\le2$, $\operatorname{Var}\psi'\le4/\epsilon$. The difference quotient proof for the two factors in the preceding note now costs at most $2S+3/w+7/\epsilon$, besides $18$ for the scalar Fresnel error. Both tails are bounded just as there; the same finite $uj$ set may be used before the replacement. Conversely every saddle with nonzero cutoff and $t_s\le t_0\le2T$ is included.

Pricing the errors by the actual stationary support removes a large power of $d$. At fixed $j$, $\sum_{u\le C/(dj),(u,q)=1}u^{-\sigma}\le[\eta/(1-\sigma)+C_\sigma](C/(dj))^{1-\sigma}$ where $C_\sigma$ is the already verified power-prefix constant; the sum vanishes when the upper limit is below one. Sum $|c_q(j)|j^{2\sigma-2}$ through the maximal reflected cutoff $y'_{\max}$ with one exact period and its discrepancy, then sum the restricted $d^{-1}$ through $C$ by partial summation. Include the two conjugates and the factors $q^{-1/2}N_{t_s}^{-a/2}$. All time errors on $d>D_0$ total less than $4.78901\,10^8$.

## Completing the longer variable

For fixed $d$ the saddle sum has scalar $(4\pi/q)\mu(d)\Omega(d)d^{-a}$ and atoms $u^{-a}\mathbf1_{(u,q)=1}c_q(j)e^{-2\pi i duj/q}$ with the raw and temporal cutoffs already stated. Split into $u\le j$ and $j<u$. Complete only the longer variable in its period.

* For $u\le j$, the short $u$ is a unit. At fixed $u$ the $j$-coefficient has mean one, by the complete-period calculation with $s=1$.
* For $j<u$, complete the unit indicator times the oscillation in $u$. At fixed $j$ its mean is $c_q(j)/q$. After the outer coefficient this gives the positive weight $c_q(j)^2/q$.

For a fixed cutoff and time-weight level the long variable is in one interval. In the second case Abel summation with its decreasing $u^{-a}$ costs at most $j^{-a}$ times the ordinary interval discrepancy. Both groups have short integer index $k\le\sqrt{N_{2T}/d}$. The trigonometric discrepancy table is certified by flooring the sine and cosine of each rational angle on the $2^{-25}$ grid. The running complex prefix ranges bound differences over every interval by their Euclidean diagonal, including zero as a prefix. The real and imaginary coordinate errors on a period of the $j$-sequence are at most $2\sum|c_q|/2^{25}$ each, and on the $q$-scaled $u$-sequence at most $2q^2/2^{25}$ each. The implementation charges four times these unscaled masses before its division. Whole periods are exact after centering. Taking complements deals with wraparound. Add one for the possible difference of a unit-bounded mean against integer count and length. Thus the first discrepancy is at most the tabulated $D_J$ uniformly on unit frequencies. In the second use $D_U((j,q))$, maximizing over all unit multiples of $j$ modulo $q$.

In either case the actual interval is contained in $(0,N_{2T}/(dk)]$. The first discrepancy is also bounded by $(1+C_*)N_{2T}/(dk)$, where $C_*$ is an upper bound for $\sum_{j\le y}|c_q(j)|/y$ from one complete period. The second is bounded by $2N_{2T}/(dk)$, before multiplication by $|c_q(k)|$. Fix $k$, let $B$ be the applicable discrepancy and $b$ the coefficient $1$ on unit indices or $|c_q(k)|$. After ignoring signs the cost over the remaining unit $d>D_0$ is at most
\[
 b k^{-a}\left(\eta\int_0^{N_{2T}/k^2} x^{-a}
          \min(B,cN_{2T}/(kx))\,dx+2^{\omega(q)}B/D_0^a\right),
\]
where $c=1+C_*$ or $2$. This is partial summation of a decreasing function against the unit count, with the finite lower endpoint retained only in the discrepancy. Evaluate the integral exactly through $k=32q$. For the rest use the constant $B$ and the nonnegative periodic sequence $bB$: its mean times the decreasing integral plus its one-period discrepancy bounds its $k^{a-2}$ and $k^{-a}$ sums. With the original scalar $4\pi/q$ the complete arithmetic error costs less than $3.5441220\,10^9$.

## The Möbius sum on the other index

In the $u$-short group keep the genuine $u$ and change variables $j=N_t/(du)$ in the continuous long integral. At fixed $t,\alpha,u$ the remaining $d$ run from $\max(D_0,y/u)$ to $N_t/u^2$ with positive decreasing weight $\Omega(d)d^{-a}$ multiplying $\mu(d)/d$. Here $u\le y$ and $(u,q)=1$. For $B_0\ge\sup_{v\ge D_0-1}|\sum_{n\le v,(n,q)=1}\mu(n)/n|$, partial summation gives $2B_0(y/u)^{-a}$. The resulting cost is bounded by $4B_0 H_q(\sqrt{N_{2T}/D_0})\int V(t)\mathbb E[y^{-a}]dt$. In the $j$-short group instead put $u=N_t/(dj)$. The $d$ lie in the interval from $\max(D_0,y'/j)$ to $N_t/j^2$ with weight $\Omega(d)$. Bound its reciprocal Möbius sum by $2B_0$. The remaining power prefix is the actual $\sum_{j\le y'}c_q(j)^2j^{a-1}/q$, bounded above by $\eta(y')^a/a$ plus the certified finite prime-product error from [the reflected diagonal](QUARTER_DIAGONAL.md). These two costs are below $4.732868\,10^9$ and $5.05184\,10^8$.

For $D_0-1\le v\le10^7$ compute every restricted reciprocal Möbius prefix. Each rational term is rounded down in units $2^{-44}$ and the final enclosure adds at most $10^7/2^{44}$. For $v\ge10^7$ use $M_q(v)=\sum_{h\mid q^\infty}M(v/h)/h$. Through $h=10^{14}$ use a certified uniform bound for $|M(x)|$ at all $x\ge 10^7/h$. This comes from Ramaré's $1/(69\log x)$ for $x\ge96955$, and every smaller ordinary signed prefix through $10^5$, in the same integer rounding. For $h>10^{14}$ use $|M|\le1$ and subtract the finite reciprocal mass from $q/\varphi(q)$. This gives $B_0<.006837457$. [Ramaré's original estimate](https://ramare-olivier.github.io/Maths/mcom2914.pdf).

The sum of the four large-$d$ costs and the genuine small-$d$ integral is below $-1.88114997\,10^{10}$. Finally add at most $2.0522030\,10^7$ for its previously priced nonstationary part, restricted to $e=1,d>D_0$. The result covers the complete row. Other mollifier rows, mixed products and the remaining near diagonals are open.

~~~powershell
python -B round8/critical/quarter_fresnel.py
python -B round8/critical/quarter_long_row.py --cut 100000
~~~

2026-11-20. Joint Claude and Codex project.
