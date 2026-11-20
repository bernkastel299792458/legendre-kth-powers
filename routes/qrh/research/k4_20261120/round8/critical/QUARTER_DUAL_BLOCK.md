# Whole low product-frequency block of the reflected self-correlation

Take the same $T=e^{37}$, $a=1/2$, $q=2310$ and log-average of the AFE as in [the signed forward block](QUARTER_SIGNED_BLOCK.md). The new verifier removes all distinct reflected product pairs $m,n\le N$; $N$ may exceed the full length $X=e^{6.5}T$ of the mollifier.

Let $N_t=qt/(2\pi)$, $y'=N_t^{1/2}/\alpha$. For the reflected squared norm conjugate its raw polynomial inside the modulus, before multiplying it by the mollifier. Thus the actual coefficient at product frequency $n$ is, up to its common scalar phase,
\[
 q^{-1/2}N_t^{-a/2}c_q(n)n^{-\sigma}
 \sum_{\substack{k\mid n,\ k\le y'\\(n/k,q)=1}}
        \mu(n/k)\Omega(n/k)k^a.
\]
Write $n=Vn_0$, where $V$ contains all prime powers of $n$ at primes dividing $q$. Each contributing $k$ is precisely $Vi$ with $i\mid n_0$ and $i\le D_V=y'/V$. Upon dropping signs and expanding the square, the sum over $n_0$ contains the unit progression
\[
 \sum_{\substack{n_0\le N/V\\[i,j]\mid n_0\\(n_0,q)=1}} n_0^{-a}
 \le \frac{(N/V)^{1-a}}{[i,j]}
    \left[\frac{\eta}{1-a}+C\left(\frac{y_{\max}'^2}{N}\right)^{1-a}\right].
\]
Here $C$ is the unit power-prefix constant previously certified at $a=.5$, since $V[i,j]\le y_{\max}'^2$. Put $A=\eta/a$. For $1\le d\le y_{\max}'$ the divisor lattice remaining after this progression satisfies
\[
 S_a(d)=\sum_{\substack{i,j\le d\\(ij,q)=1}}\frac{(ij)^a}{[i,j]}
 =\sum_{\substack{h\le d\\(h,q)=1}}\varphi(h)h^{2a-2}
       \left(\sum_{\substack{u\le d/h\\(u,q)=1}}u^{a-1}\right)^2.
\]
Squaring $A(d/h)^a+C$ and using $\varphi(h)\le h$ gives
$S_a(d)/d^{2a}\le A^2H_q(y_{\max}')+2AC/(1-a)+C^2$ for $a=.5$. The cross term uses $\sum_{h\le d}h^{a-1}\le d^a/a$, and the last uses $\sum_{h\le d}1\le d$. After multiplying by $D_V^{2a}$ the total $V$-factor in the original normalized coefficient energy is exactly
\[
 \frac1q\sum_{V\mid q^\infty}\frac{c_q(V)^2}{V}=1 .
\]
Indeed the local factor before division by $q$ is $1+(p-1)^2/(p-1)=p$. Consequently the complete weighted energy $\sum_{n\le N} n|c_n(t)|^2$ is bounded by $J$, the product of the two bracketed constants, $N^{1-a}$, and $(e^w/\alpha_0)^{2a}$, uniformly over the chosen $t,\alpha$. The common real scalar $N_t^{-a/2}$ is included in this $J$.

More generally inserting $1/W_n$, with $W_n=\prod_{p\mid(n,q)}u_p$, multiplies this computed energy bound by $\prod_{p\mid q}(1/p+(p-1)/(pu_p))$. Use $u_2,u_3,u_5,u_7=1.625,3.75,10.5,18$, $u_{11}=1$, with [the previously certified periodic Hilbert norm](ENDPOINT.md) $117.354$. The ordinary unrestricted norm $\pi$ is also valid. For the bounded remainder $.118(\sum |c_n|)^2$ set $u_p=p-1$. Factor Cauchy as $(\sum n|c_n|^2/W_n)(\sum W_n/n)$. Expanding $W_n=\prod(1+(u_p-1){\bf1}_{p\mid n})$ shows $\sum_{n\le N}W_n/n\le(1+\log N)\prod(1+(u_p-1)/p)$. The two products combine to $\prod_{p\mid q}4(p-1)/p^2$.

In the log-cutoff sweep the common time factor is $N_t^{-a}$. For the ordinary endpoint variations use
\[
 \int_{t_s}^{2T}t^a\,|d(t^{-a}V(t))|
 \le2+a\int_0^\infty V(t)\,dt/t,
\]
where the left includes the boundary jumps. The moving cutoff endpoints cost their earlier $1/(2w)$ times the same logarithmic integral. Thus multiply the normalized endpoint form by $2+(a+1/(2w))(\log(1.01T/K)+1/(2P)+1/2048)$.

At $\alpha_0=64$, $w=.75$ the [verifier](quarter_dual_block.py) bounds the entire reflected off-diagonal with $m,n\le32T$ by $7.683\,10^8$. Adding this to the [forward and stationary calculations](QUARTER_FAR_PAIRS.md), the signed allowance on the remaining narrow pairs exceeds $9.4462\,10^9$. Choosing $m,n\le1024T>X$ costs less than $3.7400\,10^9$ instead, leaving a sufficient signed allowance above $6.4744\,10^9$. Costs are at this ordinate only. High near-diagonal products and the remaining genuine stationary region are open.

~~~powershell
python -B round8/critical/quarter_dual_block.py
~~~

2026-11-20. Joint Claude and Codex project.
