# Genuine AFE interference on three complete primitive denominators

Fix \(q=2310,T=e^{37},\sigma=3/4,a=2\sigma-1=1/2,\alpha_0=64,w=.75\). Keep the mollifier, the true averaged approximate functional equation and the time window of [the completed first row](QUARTER_LONG_ROW.md). Write \(d=gr,e=gs\) with \(r>s,(r,s)=1\). Over \(s\in\{1,13,17\}\) the genuine physical cross term, with both conjugates, is less than \(-27\,478\,716\,220\). Every eligible \(g,r\) and both moving raw indices are included. The estimate is for the representative time integral at \(T=e^{37}\).

| Primitive denominator | Small-ratio integral | Tail time error | Tail lattice error | Short forward, short reflected | Total, before common far-time cost |
|---|---:|---:|---:|---:|---:|
| 1 | −35.592697299 | .546579120 | 2.370248365 | 1.551062816, .303382906 | −30.821423 |
| 13 | .787850147 | .148427136 | .865297722 | .019476281, .002457629 | 1.823509 |
| 17 | .547751796 | .130700235 | .805909489 | .012619819, .001695594 | 1.498677 |

Entries are in billions. The first row and the last column are rounded for display. The combined bound includes \(20\,522\,030\) once for all far-time pieces not evaluated with the complete small ratios. In the [remaining-band budget](QUARTER_DUAL_BLOCK.md) the global far allowance is already reserved. With these three denominators removed the remaining two high-frequency near diagonals and the interference at all other primitive denominators have a combined sufficient threshold exceeding \(36.94\,10^9\). These remaining terms are open.

## Arithmetic weights and the finite head

Write \(u_*=1+a,P=qs,N_t=qt/(2\pi),R=r/s\). The true saddle has phase \(e(-ruj/P)\) and scalar \((4\pi/q)r^{-a}/s\) before the common multiplier in \(g\), unit indicator on the raw \(u\), and weight \(u^{-a}c_q(j)\). A unit \(r\bmod P\) permutes frequencies having each prescribed gcd with \(P\). The mean in the longer variable is \({\bf1}_{s\mid u}\) if \(u\) is the short unit; in the other orientation it is \({\bf1}_{s\mid j}c_q(j/s)/q\) before the factor \(c_q(j)\). This follows by putting \(c_q(j)=\sum_{h\bmod q}^*e(hj/q)\). The mean in \(j\) counts the solutions of \(hs\equiv ru\bmod qs\), and the mean in \(u\) follows by taking complete \(q\)-blocks. Since \((q,s)=1\), \(c_q(j/s)=c_q(j)\) when \(s\mid j\).

The relative multiplier on each base pair \((r,s)\) is \(\mu^2(g)g^{-u_*}\Omega(gs)\Omega(gr){\bf1}_{(g,Pr)=1}\), with sign \(\mu(s)\mu(r)\). Its untapered mass is \(W_s\prod_{p\mid r}(1+p^{-u_*})^{-1}\), where \(W_s=\zeta_P(u_*)/\zeta_P(2u_*)\) and \(\zeta_P(v)=\prod_{p\nmid P}(1-p^{-v})^{-1}\). The mass lost to either cutoff is at most \((r/Y)^a(1/a+r/Y)\) when \(r\le sD_0\), \(D_0=10^5,Y=e^{34}\), by integrating \(g>Y/r\). The common continuous scalar is \((s^{-a}-r^{-a})/(sr)\) times the signed mass. On the finite head each Euler factor is rounded down on a \(2^{-24}\) grid and each product on a \(2^{-34}\) grid. Fewer than 24 factors suffice, so \(24(2^{-24}+2^{-34})W_s\) bounds the loss. The code applies the lower or upper scalar according to its actual sign. The Fresnel errors use the upper mass and normalization \((rs)^{-\sigma}\) from [the signed saddle proof](QUARTER_NEGATIVE.md).

For the arithmetic remainder on the finite head let \(D_J(v)\) majorize the discrepancy of the raw \(j\) sum, including its integral mean, putting the cost zero for nonunit \(v\bmod q\). Set \(\bar D=P^{-1}\sum_{v\bmod P}D_J(v)\), \(D_*=\max D_J\). For fixed \(r\) and \(y_f=\max_t y\),
\[
 \sum_{u\le y_f}\frac{D_J(ru)}{\sqrt u}
 \le 2\bar D\sqrt{y_f}+2\sqrt{D_*P\bar D}.
\]
Indeed the prefix count is bounded by \(\bar D x+\min(D_*x,P\bar D)\); Abel integration, or extending the boundary remainder to infinity, gives the displayed constant. The other outer-unit discrepancy from the signed saddle proof is unchanged, since the mean lives at \(u=sk\), with \(k\) unit. It is bounded by its prior constant times \(R^a\); after converting its coefficient the combined scalar on these errors is \(r^{-a}/s\).

## Complete periods and every large ratio

Let \(b_j=c_q(j)\) or \({\bf1}_{(j,q)=1}\). For fixed frequency \(v\) put \(\xi=e(v/s)\), \(B_l=\sum_{j=1}^l b_je(vj/P)\), \(0\le l\le q\). When \(\xi\ne1\) the prefix at \(nq+l\) is
\[
 C+\xi^n(B_l-C),\qquad C=B_q/(1-\xi).
\]
Any interval sum is therefore at most \(2\max_l|B_l-C|\). When \(\xi=1\) subtract the exact mean and bound the diameter by the diagonal of the coordinate ranges. Add one to allow a real interval length instead of the number of integers. Frequencies of opposite signs have the same discrepancy. In the implementation the second sequence is first multiplied by \(q\), keeping the exact mean integer. Normalize at the end.

The integer sine and cosine coordinates use scale \(2^{20}\). Every period prefix has vector error at most \(2\sum|b_j|\) on the unnormalized grid (the lower endpoint of each Arb ball is floored). The estimated center consequently has additional error at most \(2\sum|b_j|/|1-\xi|\). The extra \(23176\) accommodates center rounding and reduction of each coordinate by flooring at grid \(16384\), since \(16384\sqrt2+4<23176\). Include \(l=0\) separately. The code asserts that the squared coordinates fit signed 64-bit arithmetic. All subsequent norms and all trigonometric values use Arb.

For \(r>sD_0\) use the [inner stationary-time cutoff](QUARTER_LONG_ROW.md) and split into \(u\le j\), \(j<u\). Time errors have factor \((rs)^{-\sigma}(s/r)^{1-\sigma}=r^{-1}s^{-a}\) after enforcing the raw product bound. In the remaining logarithmic \(r\) sum the support and lower bound are both scaled by \(s\), while the unit discrepancy divided by \(sD_0\) only decreases. The old time price may thus be multiplied by \(W_s/s^a\).

Put \(N=sN_{2T},B=sD_0,\eta_P=\varphi(P)/P\). For each short raw index \(k\), the longer-index interval has discrepancy
\(\min(D(v),cN/(rk))\), \(v=rk\), with \(c=1+\sup_x\sum_{j\le x}|c_q(j)|/x\) in the first group and \(c=2\) in the second. Let \(d\) be the average of \(D(v)\) over the gcd orbit of \(k\). In each unit \(r\) class modulo \(P\), partial summation gives a decreasing integral divided by \(P\) plus its value at \(B\). Averaging the integrals is valid since \(\min(x,cN/(rk))\) is concave in \(x\); the sum of endpoint errors is at most \(\varphi(P)d/\sqrt B\). The verifier uses \(\varphi(P)+2^{\omega(P)}\). With \(y=N/k^2\), the combined price before the scalar \(4\pi W_s/(qs)\) is at most
\[
 \frac b{\sqrt k}\left\{\eta_P\int_B^y x^{-1/2}\min(d,cN/(kx))\,dx+
            \frac{(\varphi(P)+2^{\omega(P)})d}{\sqrt B}\right\}.
\]
Here \(b={\bf1}_{(k,q)=1}\) or \(|c_q(k)|\). Evaluate at the exact break in the integral for \(k\le2P\). For larger \(k\) replace the minimum by \(d\) and extend its lower limit to zero. The positive \(P\)-periodic sequence \(b d\) has partial-sum discrepancy at most its period mass. The remaining two decreasing power sums are bounded by their mean integral and this discrepancy, as in the completed first row.

## Möbius estimates on the continuous longer index

At each \(t,\alpha\) put \(y=\alpha\sqrt{N_t}\), \(y'=\sqrt{N_t}/\alpha\). The nonzero means occur at short raw index \(sk\). Substituting the real longer variable gives the following two quantities, with the integrals against \(2V(t)\,dt\,d\log\alpha/(2w)\). In both, \((r,Pg)=1\), the lower cutoff is combined with \(sD_0\), and the upper cutoff is \(B_1=N_t/(sk^2)\).
* For forward-short \(sk\le y,(k,q)=1\), the summand has factor \(s^{-1-a}k^{-1-a}\), followed by \(\sum_{r\ge y/k}\mu(r)\Omega(gr)/r^{1+a}\).
* For reflected-short \(sk\le y'\), its factor is \(N_t^{-a}c_q(k)^2 k^{a-1}/(qs)\), followed by \(\sum_{r\ge y'/k}\mu(r)\Omega(gr)/r\).

In either case retain the factor \(\mu(s)\mu^2(g)\Omega(gs)/g^{u_*}\). Let \(A\) be the actual lower endpoint, \(B_1\) the upper. A positive decreasing taper is an average of additional upper cutoffs, so uniform estimates on every interval \([A,v]\), \(v\le B_1\), apply. With \(h_0=10^{16},\epsilon=.006688/\log h_0\) write
\[
 C_h=W_s\prod_{p\mid P}(1-p^{-h})^{-1}
       \prod_{p\nmid P}\left(1+\frac1{(p^{u_*}+1)(p^h-1)}\right).
\]
The ordinary summatory Möbius function is at most \(\sqrt x\) through \(h_0\) and at most \(\epsilon x\) above \(h_0\). Inserting the omitted Euler factors, then summing nonnegative \(g\) weights, majorizes the restricted summatory function in absolute value by \(C_{1/2}\sqrt x+C_1\epsilon x\,{\bf1}_{x\ge h_0}\). The product for \(C_h\) uses primes through \(1000\); the omitted logarithm is at most \(1000^{1-u_*-h}/[(u_*+h-1)(1-1000^{-h})]\). Abel summation at both endpoints gives
\[
 A^a\left|\sum \mu(r)/r^{1+a}\right|_{\rm av}
 \le 2.5C_{1/2}/\sqrt A+
     4\epsilon C_1 \min(1,(A/h_0)^a){\bf1}_{B_1\ge h_0},
\]
\[
 \left|\sum\mu(r)/r\right|_{\rm av}
 \le 3C_{1/2}/\sqrt A+\epsilon C_1[2+\log(B_1/h_0)]{\bf1}_{B_1\ge h_0}.
\]
The subscript denotes summing absolute estimates over the \(g\) weights with the admissible \(r\) depending on \(g\). The factors \(2.5,3,4\) retain the endpoint cancellation between the positive decreasing integral and its far-end power. [Ramaré and Zuniga Alterman, (5), (9), Theorem 1.1 and Corollary 1.2](https://arxiv.org/pdf/2408.05969)

An independent reciprocal-prefix estimate also bounds each left side by \(2\beta_s(A)\). Write \(m_q(x)=\sum_{n\le x,(n,q)=1}\mu(n)/n\); let \(b_q(v)\) majorize \(\sup_{x\ge v}|m_q(x)|\). Then
\[
 \beta_s(A)\le W_s\!\sum_{(h,q)=1}\frac{b_q((A-1)/h)}h
                \prod_{\substack{p\mid h\\p\nmid s}}(1+p^{u_*})^{-1}.
\]
This uses the exact convolution adding Euler factors of \(sg\) to \(m_q\), then the squarefree mass of all \(g\) divisible by the primes in \(h\) outside \(s\). The verifier sums \(h<2^{16}\) by dyadic bins (isolating \(h=1\)) and applies the global maximum to the remaining positive Euler mass. The full mass has factor \((1-1/p)^{-1}\) at \(p\mid s\), and \(1+[(p^{u_*}+1)(p-1)]^{-1}\) outside \(P\). Values of \(b_q\) at dyadic endpoints from \(2^{18}\) through \(2^{30}\) use a segmented exact Möbius sieve. Each term is rounded towards zero on the \(2^{-52}\) grid, costing at most the number of terms divided by \(2^{52}\). Beyond this table use
\[
 |m_q(x)|\le \sqrt{2/x}\prod_{p\mid q}(1-p^{-1/2})^{-1}
 +\frac{.010032}{\log(10^{14})}\prod_{p\mid q}(1-p^{-1})^{-1}
   {\bf1}_{x\ge10^{14}},
\]
again by positive convolution with the ordinary estimates. The computation also uses the older bound \(\beta_1<.008191074\). For \(s>1\) split the extra \(s\)-power in the convolution into exponents \(0,1,\ge2\); on the first two \(A\ge sD_0\) retains the old lower cutoff. On the others the global weighted prefix costs \(<1.16\) (its Euler mass times the global \(b_q(0)<1.000001\)). This gives \((1+1/s).008191074+1.16/(s(s-1))\).

On the actual domain, take 32 geometric time cells through \(1.01T\), one more through \(2T\), and eight uniform log-\(\alpha\) cells. The integrated \(V\) is at most the minimum of the integrals of its three defining powers. The \(k\) bins grow by at most \(9/8\) between successive integral endpoints. The harmonic and \(k^{-1/2}\) weights are summed explicitly through \(50\,000\) or bounded by the exact period discrepancy plus their decreasing integrals. In the first group \(k^{-1-a}A^{-a}=k^{-1}y^{-a}\min(1,(y/(ksD_0))^a)\); this factor is evaluated with outward cell endpoints. Use the minimum of all local and global Möbius bounds on each cell. [True integrals and period normalization](QUARTER_LONG_ROW.md)

The first command replays the whole analytic certificate and the dyadic Möbius table. Omitting the option reuses the twelve integer maxima listed in the verifier. The finite sieve uses NumPy and Numba; the analytic calculation uses NumPy and python-flint.

~~~powershell
python -B round8/critical/quarter_three_rows.py --verify-table
~~~

2026-11-20. Joint project attribution to Claude and Codex.
