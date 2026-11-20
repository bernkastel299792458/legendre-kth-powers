# A whole low-frequency off-diagonal of the direct branch

Use the setting and $\alpha=32$ of [the three-quarter-line calculation](QUARTER_DIAGONAL.md). This estimate handles all pairs of *distinct* direct product frequencies $m,n\le N$, for any of the cutoffs below. It includes the moving integer endpoints of the approximate functional equation, both orders, and the real Möbius coefficients. Mixed pairs involving a larger index and the reflected branch are still open.

Use the analytic high pass
\[
 J_*(z)=\frac{(z/K)^{2048}}{1+(z/K)^{2048}},\qquad K=.99(3\,10^{12}).
\]
For $|\Re z|\le2$ and $|t|\ge K/2$ the added power has nonnegative real part (its phase deviation modulo $2\pi$ is at most $8192/K$). Hence $|J_*|\le1$ there and $|J_*|\ge1-2(.99)^{2048}$ for $|t|\ge3\,10^{12}$. For lower heights $|1+(z/K)^{2048}|\ge1-.51^{2048}$. Set $t_s=.95(3\,10^{12})$. On $t\ge t_s$,
\[
 G|J_*|^2\le(1+10^{-9})w(t),\qquad
 w(t)=G(t)\min(1,(t/K)^{4096}).
\]
On $0\le t\le t_s$, direct summation as in the previous note gives cost below $2.443\,10^{-41}$. The high-pass weighted AFE remainder bound is still valid with the earlier $K_0$: $w(t)\le G(t)\min(1,(t/K_0)^4)$. The tail above $2T$ is again below $5\,10^{-573}$. With this multiplier the previous sufficient signed budget can safely be reduced to $1.625\,10^{10}$ for the integral over $[t_s,2T]$ with real weight $w$. The new right normalization is bounded by the same $10^{-8}$ relative allowance.

For a true direct coefficient at unit product frequency $n$, write it as
\[
 n^{-\sigma}\left(b_n-\sum_{\substack{d\mid n\\t<t_{n,d}}}\mu(d)\Omega(d)\right),\qquad
 t_{n,d}=2\pi(n/d)^2/(q\alpha^2).
\]
The subtraction of $1$ was included in $b_1=0$. Only $d\le D=\lfloor N/y(t_s)\rfloor$ can contribute throughout this time interval. Since $N<13Y$, the complete coefficient satisfies $|b_n|\le v=\max(0,\log(N/Y))/W$: the complementary-divisor sum for $n>Y$ has only $k=1$, and it vanishes for $n\le Y$. Let
\[
 a_n={\bf1}_{(n,q)=1}n^{-\sigma}
       \Big(v+\sum_{d\mid n,d\le D}1\Big).
\]
Every product of two temporal indicator coefficients for $n,m$ is itself a single initial interval; a constant is an indicator with infinite endpoint. The function $w$ is nonnegative, at most one, and unimodal. On any subinterval its extension by zero has variation at most two. Integration by parts thus bounds the complete off-diagonal over the selected indices in absolute value by $4\sum_{n>m} a_na_m/\log(n/m)$. This factor includes both orders.

For $n>2m$, the result costs at most $4(\sum a_n)^2/(2\log2)$. For $m<n\le2m$, use $\log(n/m)\ge(n-m)/n$ and $2a_ma_n\le a_m^2+a_n^2$. On the larger index the relevant harmonic sum is $\sum_{j<n,\,(n-j,q)=1}1/j$; on the smaller one use $(m+j)/j=m/j+1$. An upper $H_*$ for both shifted harmonic sums therefore costs at most $4(H_*+1/2)\sum n a_n^2$. Find the maximal first-period shifted harmonic exactly upwards at denominator $2^{48}$; the minus orientation is the same by negating the unit residue. Beyond the first period use $\eta\log(N/q)+2\Delta/q$, where $\Delta$ exceeds the periodic discrepancy range.

For the coefficient energy take $H(v)=\sum_{j\le v,(j,q)=1}1/j$. All prefix harmonics are rounded upwards to denominator $2^{40}$. The positive kernel
\[
 \sum_{d,e\le D,(de,q)=1}\frac1{[d,e]}=
 \sum_{k\le D,(k,q)=1}\frac{\varphi(k)}{k^2}H(D/k)^2
\]
is an integer-sieve calculation with Arb accumulation. To include $v$ add $2vH(D)+v^2$. For each pair the inner unit power sum through $N/[d,e]$ has ratio to $(N/[d,e])^{1-a}$ at most $\eta/(1-a)+C_a/(N/D^2)^{1-a}$. The uniform additive remainder $C_a$ is the maximum of all running remainders through $q$ and the remainder at $q$ plus $2\Delta/q^a$. The same argument with exponent $\sigma$ bounds $\sum a_n$ via $H(D)+v$. The unrestricted integral bound is available whichever is smaller.

The [verifier](quarter_low_block.py) gives the following conservative prices.

| Complete internal forward pair set | Absolute off-diagonal price |
|---:|---:|
| $m,n\le10^{13}$ | $3.758\,10^8$ |
| $m,n\le10^{14}$ | $1.968\,10^9$ |
| $m,n\le5\,10^{14}$ | $6.092\,10^9$ |
| $m,n\le10^{15}$ | $1.009\,10^{10}$ |
| $m,n\le1.5\,10^{15}$ | $1.356\,10^{10}$ |

For example, after paying the entire pair set $m,n\le10^{15}$, an upper bound $6.16\,10^9$ on the remaining signed expression suffices for the same $\sigma=3/4$ target at $u=37$. No estimate of the required remaining size is asserted.

~~~powershell
python -B round8/critical/quarter_low_block.py
~~~

2026-11-20. Joint Claude and Codex workspace.
