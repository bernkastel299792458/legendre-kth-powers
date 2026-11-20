# A signed Hilbert bound for all forward pairs through eight times the ordinate

Take the parameters of [the three-quarter-line second moment](QUARTER_DIAGONAL.md) at $T=e^{37}$. Average the true two-branch AFE over $\alpha=\alpha_0 e^v$, where $v$ is uniform on $[-w,w]$, $w=.75$. The function on the left of the AFE is independent of $v$. Let $P=128$, $t_s=1.5\,10^{12}$, $K=2.25\,10^{12}$. Use the analytic high pass $J_*(s)=(s/K)^P/(1+(s/K)^P)$ and the real temporal majorant $V(t)=G(t)\min(1,(t/K)^{2P})$ from [the low block](QUARTER_LOW_BLOCK.md). The same argument gives $|J_*|\ge1-2(.75)^{128}$ at all target heights, and $G|J_*|^2\le(1+10^{-9})V$ for $t\ge t_s$.

## Recovering the signed energy on a prefix

Write $\eta=\varphi(q)/q$, $q=2310$, $a=2\sigma-1=1/2$, $Y=e^{34}$ and $y=\alpha\sqrt{qt/(2\pi)}$. For $n\le N$ the real coefficient times $n^{-\sigma}$ of the direct branch, including its subtraction of one, has numerator
\[
 b_n-\sum_{\substack{d\mid n\\d<n/y}}\mu(d)
 \quad\text{when }(n,q)=1 .
\]
Here $D=\lceil N e^w/(\alpha_0\sqrt{qt_s/(2\pi)})\rceil<Y$, so the cutoff weights on every displayed small divisor equal one. The endpoint where $n/y$ is an integer has measure zero in the log-average.

Put $\Sigma_q(x)=\sum_{d,e\le x,\,(de,q)=1}\mu(d)\mu(e)/[d,e]$. Then $\eta\Sigma_q(x)\le\Sigma_1(x)$. Indeed take the periodic mean of $(\sum_{d\mid n,d\le x}\mu(d))^2$ and of that nonnegative square restricted to $(n,q)=1$. For $422\le x<10^8$ the upper bound is $.445$ and for $x\ge 10^8$ it is at most $.6593$. Compute the finite smaller range of $\Sigma_q$ by adding one rational row and its transpose at a time. [Ramaré and Zuniga-Alterman, Theorem 1.1](https://arxiv.org/pdf/2603.25961#page=2).

Squaring the small-divisor sum and weighting by $n^{-a}$ leads to the range $y\max(d,e)<n\le N$ of unit multiples of $l=[d,e]$. Its main term is $\eta l^{-1}\int_{y\max(d,e)}^N x^{-a}dx$ for active $d,e$. Consequently its aggregate main is the exact signed integral $\eta\int_y^N x^{-a}\Sigma_q(x/y)\,dx$ when $y<N$, and zero otherwise. Define $E(x)=\sum_{j\le x,(j,q)=1}j^{-a}-\eta x^{1-a}/(1-a)$, $C\ge\max(0,\sup E)$ and $O\ge\sup E-\inf E$. The error on each pair is at most $O l^{-a}$. To certify $C,O$, check every integer and left limit through $q$, then use partial summation and the periodic unit discrepancy for the tail $|E(x)-E(q)|\le2\Delta q^{-a}$. With $b=\eta/(1-a)$ and $H_q$ the unit harmonic sum, an absolute error multiplier is
\[
 \sum_{\substack{d,e\le D\\(de,q)=1}}[d,e]^{-a}
 \le b^2D^{2-2a}\zeta_q(2-a)+2bCD^{1-a}H_q(D)+C^2(bD^{1-a}+C).
\]
In fact for $d=gj,e=gk,(j,k)=1$ one may remove the coprimality and bound the two inner sums separately by $b(D/g)^{1-a}+C$. For the other part of the coefficient use $u_k=\min(1,\max(0,\log(N/(Yk)))/W)$ at unit indices $k\le N/Y$. The complementary divisor formula yields $|b_n|\le\sum_{k\mid n}u_k$. Thus its weighted energy is at most $\sum_{j,k} u_ju_k(bN^{1-a}/[j,k]+C/[j,k]^a)$. Combine the two squared energies by Minkowski to obtain a bound $J$ for $\sum_{n\le N}n|c_n(y)|^2$, with $c_n(y)$ the actual coefficient including $n^{-\sigma}$.

## All moving endpoints

For fixed $y$, the Hilbert quadratic form with entries $1/[i\log(n/m)]$, with phases $e^{it\log(n/m)}$ and actual coefficients $c_n(y)$, has absolute value at most $B=(.915503+.118H_q(N))J$. The integer Hilbert norm in [the endpoint proof](ENDPOINT.md) holds on the unit classes modulo 210 and hence on this smaller support. The entrywise gap correction is at most $.118$, and Cauchy bounds $(\sum|c_n|)^2\le H_q(N)J$.

For the weighted time integral over $[t_s,2T]$ freeze all coefficients before performing integration by parts against the log phase. Averaging the quadratic coefficient in $v$ amounts to integrating it in $\log y$ over a window of length $2w$ translated with velocity $1/(2t)$. Its derivative is the difference of the complete two endpoint quadratic coefficients divided by $4wt$. This identity is exact as a weak derivative of the moving average of bounded step functions. Both endpoint forms have absolute value at most $B$. The zero-extended $V$ over the time interval has total variation at most 2. Therefore the entire off-diagonal, including both orders and every pair $m,n\le N$, has absolute value at most
\[
 B\left[2+\frac{\log(1.01T/K)+1/(2P)+1/2048}{2w}\right].
\]
Here the last factor comes from $\int V(t)dt/t$, extending to all positive heights for this positive integral.

## Sufficient remaining quantity

Use the probability measure $dv/(2w)$ in all three terms of the AFE. In the earlier diagonal certificate multiply the shared main term by $\sinh(aw)/(aw)$ and its direct error by $\sinh(2aw)/(2aw)$, since the latter's selected exponent is at most $2a$. The reflected remainder and the complete diagonal are independent of $\alpha$. Take Minkowski after averaging. For the AFE error constant $c$ split the interval in $v$ wherever $\alpha_0e^v\sqrt q=d$, $d\mid q$. On each subinterval $c/(2\pi)^{\sigma/2}$ is a sum of two constant multiples of $e^{(1-\sigma)v}$ and $e^{-\sigma v}$, so its average square is an elementary integral. The variation bound for the high-pass AFE error still uses $K_0$ as in the earlier note. Direct initial cost is below $1.804\,10^{-13}$, with the same remote bound as before. The [verifier](quarter_signed_block.py) subtracts the resulting cost from the $1.75\,10^{11}$ positive-time second-moment objective.

| $\alpha_0$ | Upper product index $N$ | Absolute internal off-diagonal bound | Sufficient signed budget for everything else |
|---:|---:|---:|---:|
| 64 | $T$ | $2.153\,10^9$ | $1.37685\,10^{10}$ |
| 64 | $4T$ | $5.556\,10^9$ | $1.03658\,10^{10}$ |
| 96 | $8T$ | $8.872\,10^9$ | $5.44558\,10^9$ |

In the final column the expression is the $v$-average of the entire signed non-diagonal in the previous note with real weight $V$ on $[t_s,2T]$, omitting the already bounded pairs. It includes higher forward products, pairs across the cutoff, the reflected non-diagonal and the true direct/reflected interference. Controlling that remainder is still necessary at this single height.

~~~powershell
python -B round8/critical/quarter_signed_block.py
~~~

2026-11-20. Joint Claude and Codex research workspace.
