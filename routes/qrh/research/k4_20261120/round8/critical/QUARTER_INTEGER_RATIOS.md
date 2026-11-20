# True AFE interference on every integer ratio

Use the [complete first row](QUARTER_LONG_ROW.md) with $q=2310,T=e^{37},a=1/2,\alpha_0=64,w=.75$ and ratio cutoff $D_0=10^5$. The [integer-ratio verifier](quarter_integer_ratios.py) includes every true pair $d=gr,e=g,r\ge2$ for which both mollifier weights are nonzero. The phase and the two raw cutoffs depend only on $r$. Relative to the first row, for squarefree $g,r$ the multiplier is
\[
 \mathbf1_{(g,rq)=1}\mu(g)^2g^{-1-a}\Omega(g)\Omega(gr)
\]
with the common sign $\mu(r)$. Write $u=1+a$, $W_0=\zeta_q(u)/\zeta_q(2u)$. For $r\le D_0$ the sum of those nonnegative multipliers is at most $W_r=W_0\prod_{p\mid r}(1+p^{-u})^{-1}$ and at least $W_r-(r/Y)^a(1/a+r/Y)$. Indeed both tapers equal one through $g\le Y/r$, and the remaining untapered tail admits the first-term bound plus a decreasing integral. Use the lower sum for the negative scalar, the upper for the positive one and $W_r$ on all errors. This complete smaller-ratio integral is below $-3.20836432\,10^{10}$.

At larger $r$ multiply the positive time and lattice errors of the first-row proof by $W_0$. In the two intervals with continuous longer index, for each fixed $g$ the variable $r$ must be coprime to $qg$, with positive decreasing taper $\Omega(gr)$. Replace $B_0$ in their bounds by
\[
 \mathcal B=\sum_{(g,q)=1}\frac{\mu(g)^2}{g^u}
 \sum_{h\mid g^\infty}\frac{b((D_0-1)/h)}h
 =W_0\sum_{(h,q)=1}\frac{b((D_0-1)/h)}h
                 \prod_{p\mid h}\frac1{1+p^u}.
\]
Here $b(x)$ bounds $|M_q(t)|$ for all $t\ge x$. The reduction uses $M_{qg}(t)=\sum_{h\mid g^\infty}M_q(t/h)/h$. Summing the squarefree $g$ over multiples of $\operatorname{rad}(h)$ gives the second equality.

Compute through $h=10^5$ using the certified prefixes of [the first-row proof](QUARTER_LONG_ROW.md). The full positive Euler mass without $b$ is $\prod_{p\nmid q}(1+1/((p^u+1)(p-1)))$. Evaluate its factors through $10^4$, bounding the omitted logarithm by $(10^4)^{-u}/(u(1-10^{-4}))$. Subtract the computed head and apply the uniform prefix supremum on the tail. This gives $W_0<1.1413220$ and $\mathcal B<.008191073$. The large-ratio time, lattice and two continuous costs are below $.546580\,10^9$, $4.044985\,10^9$ and $6.275032\,10^9$. Adding the whole nonstationary allowance $.020523\,10^9$ proves an upper below $-2.11965260\,10^{10}$ for the **entire physical integer-ratio cross term**. The distinct nonintegral ratios and the other high products remain.

~~~powershell
python -B round8/critical/quarter_integer_ratios.py
~~~

2026-11-20. Joint Claude and Codex research project.

## Sign of the complementary continuous term

Normalize the continuous stationary model by $(2\eta/a)\int V(t)\mathbb E[y^{-a}]dt$. In this normalization its full value is $R-S_{\max}$ by [the stationary identity](QUARTER_STATIONARY_MAIN.md). Its integer-ratio part is $A-B$, where
\[
 A=\sum_g\frac{\mu^2(g)\Omega(g)}{g^{1+a}}\!
     \sum_{(r,gq)=1}\frac{\mu(r)\Omega(gr)}r,\qquad
 B=\sum_g\frac{\mu^2(g)\Omega(g)}{g^{1+a}}\!
     \sum_{(r,gq)=1}\frac{\mu(r)\Omega(gr)}{r^{1+a}},
\]
with $g$ restricted to $q$-units. The term $r=1$ cancels in their difference. Without the tapers, $B=1$ exactly: for each squarefree unit $n=gr$, its summands give $n^{-1-a}\sum_{r\mid n}\mu(r)$. All changed coefficients have $n>Y$, so $|B-1|\le Y^{-\theta}\zeta_q(1+a-\theta)^2$ for $0<\theta<a$. At the row in question $|B-1|<.000005120$.

The bound on $A$ uses the reciprocal Möbius estimate of [the previous note](QUARTER_STATIONARY_MAIN.md). For fixed $g$, expand the $qg$-restricted reciprocal sum as the ordinary one over $h\mid(qg)^\infty$. Use $1/(69\log B_*)$ when $gh\le Y/B_*$, $B_*\ge96955$, and $(B_*gh/Y)^\theta$ times the unit bound otherwise. Put $u=1+a$ and
\[
 E(\theta)=\exp\left(\frac{13^{-v}+13^{1-v}/(v-1)}{1-13^{-1+\theta}}\right),
 \quad v=u+1-2\theta.
\]
The small part costs at most $(q/\varphi(q))W_0 E(0)/(69\log B_*)$. The large part costs at most $(B_*/Y)^\theta\zeta_q(u-\theta)E(\theta)\prod_{p\mid q}(1-p^{-1+\theta})^{-1}$. This follows by summing squarefree $g$; the extra prime-factor logarithm is bounded by $p^{-u-1+2\theta}/(1-13^{-1+\theta})$. Thus $|A|<.015987878$.

Reevaluating the finite signed $S_{\max}$ through $2^{22}$ costs an absolute upper tail below $.018050921$. The [verifier](quarter_other_main.py) therefore places the **normalized nonintegral-ratio continuous term** strictly between $.00534356$ and $.109717994$. This is a positive contribution of the continuous model. Its true oscillatory/lattice error is still open for these nonintegral ratios.

~~~powershell
python -B round8/critical/quarter_other_main.py
~~~
