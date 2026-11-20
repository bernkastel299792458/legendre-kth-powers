# Real coefficients of the three-quarter-line mollified second moment

Fix $q=2310$, $T=e^{37}$, $Y=e^{-3}T$, $X=e^{9.5}Y$, $a=2\sigma-1=1/2$, $\Omega(d)=\min(1,\max(0,\log(X/d)/9.5))$. Write $M(s)=\sum_{(d,q)=1}\mu(d)\Omega(d)d^{-s}$, $Z(s)=\zeta(s)E_q(s)$, and $f=ZM-1$. All estimates in this file are unconditional arithmetic or integral inequalities. The remaining signed integral below has **not** been bounded. The new semi-infinite prime-interval coverage in [the moving-line proof](MOVING_LINE.md) is independent of this criterion.

On the representative Gabriel row, replacing the left endpoint by a true second moment at $\sigma=3/4$ makes both endpoint exponents two. The polynomial $1-f^2$ vanishes at $f=-1$ and obeys $\log|1-f^2|\le |f|^2$. At $s=.84$, preserving the right edge $R=1+1.1/37$ and its same detector, the sufficient left integral $1.75\,10^{11}$ is below the old break-even value $1.7593\,10^{11}$. This follows by isolating the left integral in the first display of [the interpolation calculation](MOVING_LINE.md) with $\nu=2$, $j(2)=1$, $P=(R-s)/(R-3/4)$. The suppressed high-pass factor described below costs below $10^{-9}$ relatively. The threshold applies to this actual height and detector; it is not an assertion of full intermediate-height coverage.

## Complete squared diagonal of the Dirichlet coefficients

Let $b_n$ denote the Dirichlet coefficients of $f$, so $b_1=0$, $b_n=0$ if $(n,q)>1$, and $b_n=\sum_{d\mid n}\mu(d)\Omega(d)$ otherwise. For $n>1$ use $\sum_{d\mid n}\mu(d)=0$ and take the complementary divisor $k=n/d$. Only $k<n/Y$ survives, with absolute weight at most $\min(1,\log(n/(Yk))/W)$, $W=9.5$. For a pair $k,l$ the product of these weights is at most $g(\log(n/B))$ where $B=Y\sqrt{kl}$ and $g(x)=\min(1,x^2/W^2)$ for $x\ge0$, zero otherwise. This is the geometric-mean inequality for two nonnegative logarithms. The resulting $n$ are multiples of $D=[k,l]$, coprime to $q$.

The function $n^{-1-a}g(\log(n/B))$ is unimodal. Integrating its superlevel intervals over the lattice $D\mathbb N$ bounds the total by the uniform average integral and one peak. For unit indices modulo $q$ its density is $\eta=\varphi(q)/q$ with interval counting error at most $\Delta$, computed as one plus the range of the normalized periodic counting discrepancy. In units $B^{-a}/D$, the normalized continuous integral is
\[
 I=\int_0^\infty e^{-ax} g(x)\,dx=
 {2[1-(1+aW)e^{-aW}]\over a^3W^2}.
\]
Let $P_b=\max_{x\ge0}e^{-bx}g(x)$, attained at $\min(W,2/b)$. Because every actual $n$ is at least $D$, the normalized sampled peak is bounded by both $P_a$ and $(D/B)P_{1+a}$. For $0\le e<a$, bound it by their weighted geometric mean. Write $\zeta_q(z)=\zeta(z)\prod_{p\mid q}(1-p^{-z})$. The positive Euler sum needed is
\[
 C(e)=\zeta_q(1+a){\zeta_q(1+(a-e)/2)^2\over\zeta_q(2+a-e)} .
\]
Indeed for $k=gx,l=gy,(x,y)=1$ the extra factor $(D/\sqrt{kl})^e=(xy)^{e/2}$. Consequently
\[
 \sum_n |b_n|^2 n^{-1-a}\le
 Y^{-a}\{\eta I C(0)+\Delta P_a^{1-e}P_{1+a}^eY^{-e}C(e)\}.
\]
The verifier tries nine exponents and the unrestricted unit-lattice bound. Multiplication by $\int_0^\infty G(t)\,dt$ costs less than $4.350\,10^7$ for the entire physical Dirichlet-coefficient diagonal.

## Matching signed arithmetic on the direct and reflected diagonals

At time $t$ choose $y=\alpha\sqrt{qt/(2\pi)},\ y'=\alpha^{-1}\sqrt{qt/(2\pi)}$, $N(t)=yy'$. Apply the asymmetric approximate functional equation to each Euler divisor with forward cutoff $y/d$. Summing yields the forward sum over unit $m\le y$, and the reflected sum over $m\le y'$ with coefficient $c_q(m)/\sqrt q$, phase $q^{-it}(t/(2\pi e))^{-it}e^{i\pi/4}$ and modulus multiplier $N(t)^{-a/2}$. Multiplying by $M$ gives two branches. The direct branch $A$ also includes the subtracted constant $-1$. The reflected branch $B_1$ includes its phase. [Simonič, Corollary 1, equations (11)–(13) and Table 2](https://arxiv.org/pdf/1910.08274#page=4)

For the forward branch its coefficient vector is the full $b_n$ minus the convolution removed by $m>y$. Put $w_d=\mu(d)\Omega(d){\bf1}_{(d,q)=1}$ and define
\[
 S=\sum_{d,e}\frac{w_dw_e}{[d,e]\max(d,e)^a}.
\]
For the removed vector its exact squared diagonal uses the inner factor
\[
 [d,e]^{-1-a}\sum_{\substack{k>y\max(d,e)/[d,e]\\(k,q)=1}} k^{-1-a}.
\]
The continuous term is $\eta S y^{-a}/a$. The unit-progression tail differs from $\eta x^{-a}/a$ by at most $C x^{-a-\epsilon}$ for $0<\epsilon<\min(1,a)$ and $C=\max(2\sup|\#\{n\le x:(n,q)=1\}-\eta x|,\zeta_q(1+a)+\eta/a)$. This follows by Abel summation above $x=1$ and the positive zeta sum below it. After inserting all pairs the absolute error is at most $C y^{-a-\epsilon}C(\epsilon)$ since $[d,e]/\max(d,e)\le\sqrt{xy}$ for $d=gx,e=gy$. To bound the actual forward diagonal, add the square roots of the removed and full diagonal bounds in the joint $(t,n)$ square norm.

For the reflected squared norm take the ordinary product of the two series inside the modulus, conjugating the reflected polynomial if needed; their coefficients are real. At frequency $n$ the unphased coefficient is
\[
 {c_q(n)\over\sqrt q} n^{\sigma-1}
 \sum_{\substack{d\mid n\\n/d\le y'}} w_d d^{-a}.
\]
Here $c_q(n/d)=c_q(n)$ for unit $d$. On expanding its diagonal the inner partial sum is $q^{-1}\sum_{j\le y'\min(d,e)/[d,e]}c_q(j)^2 j^{-1+a}$, multiplied by $(de)^{-a}[d,e]^{-1+a}w_dw_e$. The positive expansion
\[
 c_q(j)^2=\sum_{k\mid(q,j)}\prod_{p\mid k} p(p-2)
\]
and $0\le u^a/a-\sum_{j\le u} j^{-1+a}\le1/a$ bound the deviation of that inner sum from $\eta u^a/a$ by $K=(aq)^{-1}\prod_{p\mid q}(1+(p-2)p^a)$. On restoring $N(t)^{-a}$ the main term is **the same $\eta S y^{-a}/a$**. This equality concerns the diagonal arithmetic. Cancellation against a cross-term of the full oscillatory mean would require a separate estimate.

Its absolute remainder is at most $K N(t)^{-a}\zeta_q(1+a)H_q(X)^2$, where $H_q(X)$ is the unit harmonic sum. Indeed the gcd decomposition $d=gx,e=gy$ leaves $g^{-1-a}/(xy)$, and $x,y\le X$. Use an exact harmonic prefix at 65536 and elementary periodic Abel bounds above it.

For $S$, the squarefree signed submatrix $d,e\le 262144$ has all $\Omega=1$. The elementary identity $(d,e)=\sum_{l\mid(d,e)}\varphi(l)$ gives a running prefix over each divisor. The program stores $\lfloor 2^{96}\mu(d)/d\rfloor$ and charges an absolute aggregate error $2(262144)^2/2^{96}$ at the end. On the rest, drop signs and use the positive bound
\[
 2\sum_{\substack{g,x\ge1\\gx>262144\\(gx,q)=1}}(gx)^{-1-a}H_q(x).
\]
Dyadic unit counts through $2^{70}$ and integral estimates for both infinite tails give $S<.996552$. For the $[0,T]$ average replace $t^{-b}$ by $T^{-b}/(1-b)$. The flat positive-time weight $G(t)=\min(1,(1.01T/t)^{2048})$ costs at most a further $1.01(2048/2047)$ since each primitive grows no faster than linearly when $Y,X$ are held fixed.

## One finite signed quantity

To suppress the initial segment while recovering the target $H\le |t|\le T$, include the analytic multiplier $J(s)=1-\exp((s/K_0)^2)$, $K_0=3000175332800/5$. On $|\Re s|\le2$, $|J|\le1+10^{-12}$. For $|t|\le K_0^2/8$ the exponential has phase at most $1/2$ and amplitude at most $\exp(4/K_0^2)$, giving modulus at most one after subtraction. At larger $|t|$ the exponential is negligible. For $|t|\ge3\,10^{12}$ the modulus of $J$ is at least $1-2e^{-25}$. At small $t$, $|J|\le (t+2)^2\exp(4/K_0^2)/K_0^2$.

Take $t_c=1+\max(1000,2\pi\max(\alpha\sqrt q,\sqrt q/\alpha)^2)$. At $t\ge t_c$ all the AFE cutoffs are at least one. Its aggregate absolute remainder before $M$ is at most $c t^{-\sigma/2}$. For $v=\alpha\sqrt q$,
\[
 c=(2\pi)^{\sigma/2}\left\{\sum_{\substack{d\mid q\\ d<v}}16 v^{1-\sigma}/d+
   \sum_{\substack{d\mid q\\d\ge v}}11v^{-\sigma}\right\}.
\]
For the unsmoothed $M(s)$, the unweighted square integral through $Z$ is $Z\sum|w_d|^2/d^{2\sigma}+O(E)$ with absolute error $E=12(1+\log X)\sqrt X+2(\sum_{n\le X}n^{-\sigma})^2/\log2$. This follows from the near/far ratio proof in [the displaced fourth-moment note](MOVING_LINE.md). The high-pass weighted error square above $t_c$ is bounded by $1.00001c^2$ times
\[
 \zeta_q(2\sigma)(1.01T)^{1-\sigma}
 (1/(1-\sigma)+1/(2048+\sigma-1))+2E K_0^{-\sigma}.
\]
For this inequality on $t\ge t_c$ use $|J|^2\le1.00001\min(1,(t/K_0)^4)$, then the weight $t^{-\sigma}\min(1,(t/K_0)^4)G(t){\bf1}_{t\ge t_c}$ has variation at most $2K_0^{-\sigma}$. On $[0,t_c]$ and $t>2T$ charge $f$ directly using $|\zeta(3/4+it)|\le12(t+2)^{1/4}$ (Euler summation at $\lceil t+1\rceil$), $|M|\le4X^{1/4}$ and the high-pass/flat weight respectively.

Use the physical weight $v(t)=G(t)|J(3/4+it)|^2$. For the two diagonal sums $\Delta_A(t),\Delta_{B_1}(t)$ just described, define
\[
 \mathcal C=\int_{t_c}^{2T}v(t)\left\{|A(t)+B_1(t)|^2
              -\Delta_A(t)-\Delta_{B_1}(t)\right\}\,dt .
\]
All sums in this expression are finite and use the true oscillatory signs. For $\alpha=32$, the sum of the two certified diagonals is below $6.301854\,10^{10}$, the AFE squared error is below $1.870222\,10^{10}$, the initial error below $2.542390\,10^6$, and the remote error below $5\,10^{-573}$. From the triangle inequality in $L^2(v\,dt)$, the single **sufficient target** is therefore
\[
                     \mathcal C \le 1.62636\,10^{10}.
\]
This would give $\int_0^\infty G(t)|J(3/4+it)f(3/4+it)|^2dt<1.75\,10^{11}$ at $T=e^{37}$. For $\alpha=16$ the corresponding sufficient target is $7.1508\,10^9$. The calculation gives no upper bound on $\mathcal C$.

~~~powershell
python -B round8/critical/quarter_diagonal.py
~~~

2026-11-20. Joint Claude and Codex research workspace. These estimates and computation were developed by Codex.
