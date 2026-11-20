# The remaining near diagonals and the stationary band

After [the signed forward prefix](QUARTER_SIGNED_BLOCK.md), the two entire self-correlations outside a narrow ratio band and the outer part of the true stationary-phase interference can be paid numerically. The [verifier](quarter_far_pairs.py) uses no sampling of the AFE phase.

Let $V_z(t)=V(t)(t/t_s)^{-z}$ on $[t_s,2T]$. For the direct, reflected and cross terms take $z=0,a,a/2$, respectively, absorbing $(qt_s/(2\pi))^{-z}$ into the respective coefficient products. Each elementary pair of direct raw indices has temporal cutoff $u_1,u_2\le\alpha\sqrt{qt/(2\pi)}$. Its average in $\log\alpha$ is a nondecreasing function $F(t)$ whose derivative is $1/(4wt)$ on one interval and zero elsewhere. The reflected branch has the same property with $\alpha$ replaced by $1/\alpha$. The subtracted constant uses no moving index. The kernel for an elementary pair is the integral of $B(t)e^{it\lambda}$, $B=V_z F$, where $\lambda=\pm\log(n/m)$ for the corresponding product frequencies. For the reflected self-correlation one may conjugate its unphased polynomial inside the modulus before multiplying by the mollifier, giving products of integer indices as in the earlier diagonal calculation.

Put $D=1.01T$, $m=2048$, $S_z=2P/K+(m+z)/D$, $Q_0=(t_s/K)^{2P}+(D/(2T))^m$. On each of the intervals split by $K,D$, $V_z$ is a single power; the two low-frequency derivative maxima sum to at most $2P/K$ and the last to $(m+z)/D$. Thus the regular derivative extended by zero has variation at most $2S_z$, by summing the variations of three one-signed monotone pieces separately. The variation of $V_z$ extended by zero is at most 2. For the self-correlations, applying the product rule gives $\operatorname{Var}_{\rm ext}(B')\le 3S_z+1/(wt_s)$. Here and below the variation of the *regular* derivative includes both boundary values by extending it by zero. Two integrations by parts give the uniform kernel bound $Q_0/|\lambda|+(3S_z+1/(wt_s))/\lambda^2$.

For the true direct/reflected product index the forward raw term by $(d,u)$, the reflected raw term by $(e,j)$, where $d,e$ are the mollifier indices. Up to conjugation,
\[
 \Phi'(t)=\xi=\log(t/t_0),\qquad t_0=\frac{2\pi d u j}{qe}.
\]
This follows by differentiating the explicit Simonič phase, including the $q^{-it}$ factor. The cutoff in $\log(\alpha/\alpha_0)$ is the intersection of $[-w,w]$ with an interval whose two ends recede at speed $1/(2t)$. Its probability $F$ is continuous and nondecreasing. Its derivative has the form $k/(4wt)$, $k=0,1,2$. After activation the number of moving ends can only decrease. Thus $\|B'\|_\infty\le S_z+1/(2wt_s)$, $\operatorname{Var}_{\rm ext}(B')\le3S_z+3/(wt_s)$ and $\operatorname{Var}_{\rm ext}(B/t)\le4/t_s$. The same bounds hold for the subtracted direct constant; one of the two ends is then absent.

For $\epsilon>0$ take $R(\xi)=\min(1,\max(0,|\xi|/\epsilon-1))$. Twice integrate $\int B R(\xi)e^{i\Phi}dt$ by parts. The first edge costs $Q_0/\epsilon$. In the second variation the two regular terms are $B'D_1+(B/t)D_2$, where $D_1=R(\xi)/\xi^2$ and $D_2=(R(\xi)/\xi)'/\xi$. Set both to zero at zero. Their suprema are at most $\epsilon^{-2},\epsilon^{-3}$ and their variations at most $4\epsilon^{-2},8\epsilon^{-3}$. In the positive transition interval $D_2=\xi^{-3}$, and beyond it $D_2=-\xi^{-3}$; reflection supplies the other wing. Monotonicity of $\xi$ preserves these variation bounds. In particular the entire nonstationary kernel costs at most
\[
 \frac{Q_0}{\epsilon}+
 \frac{3S_z+3/(wt_s)+4(S_z+1/(2wt_s))}{\epsilon^2}
 +\frac{24}{t_s\epsilon^3}.
\]
The remaining complementary weight $1-R$ is supported on $|\xi|<2\epsilon$. On that support, any nonzero pair obeys $d/e\ge e^{-2\epsilon}$ because $uj\le qt/(2\pi)$. This last restriction does not apply to the subtracted direct constant.

For the absolute atom bounds use the complete period of the unit indicator and $|c_q(j)|$ to price their decreasing power sums. For the mollifier integrate its positive cutoff majorant over $Y\le x\le X$ with measure $dx/(Wx)$, giving $C+\eta(X^{1-\sigma}-Y^{1-\sigma})/[W(1-\sigma)^2]$. Take $t=2T$ and the largest allowed $\alpha$ and $\alpha^{-1}$ to bound the forward and reflected raw lengths. Multiply the two single-branch majorants and include both conjugates for the interference; square the appropriate majorant for each self-correlation. Pairs already paid in the signed prefix may be omitted from these absolute sums.

At $\alpha_0=64,w=.75,N=4T,\epsilon=.03$ the complete forward outer-band price is below $4.670\,10^7$, the reflected one below $1.486\,10^5$ and the genuine nonstationary cross-term below $2.053\,10^7$. Consequently the signed allowance for the remaining **near-diagonal and stationary** expression exceeds $1.0298476\,10^{10}$ on the same row $T=e^{37}$. The more restrictive $\epsilon=.01$ leaves $9.6120\,10^9$. These are sufficient numerical targets; the surviving near pairs are open.

~~~powershell
python -B round8/critical/quarter_far_pairs.py
~~~

2026-11-20. Joint Claude and Codex project.

## All cross terms in one ordering of the true mollifier indices

Keep the same notation and write $s=\log(e/d)\ge0$ for this section. Before clipping the moving $\log\alpha$ interval to $[-w,w]$, its length is $\xi-s=\log(qt/(2\pi uj))$. Thus $0\le F(\xi)\le(\xi-s)_+/(2w)$. After its first positive point, $F$ is concave, nondecreasing and piecewise affine in $\xi$. In particular $H_1(\xi)=F(\xi)/\xi$, extended by zero before activation, is unimodal and at most $1/(2w)$. To see this, $\xi F'(\xi)-F(\xi)$ is nonincreasing after activation since $\xi\ge0$ there. This also holds at $s=0$, when $H_1$ may have a jump at zero.

One integration by parts against $e^{i\Phi}$ bounds the full raw oscillatory integral by $c_0=4/(2w)$, using the variation of $V_{a/2}H_1$ extended by zero. For $s>0$ retain its endpoint contribution $Q_0/(2w)$ and integrate again. The regular derivative to be divided by $\xi$ is then
\[
 V_{a/2}'\,F/\xi^2+(V_{a/2}/t)(F'_\xi/\xi^2-F/\xi^3).
\]
For $F/\xi^2$ the supremum and total variation are at most $1/(2ws)$ and $3/(2ws)$ respectively. Each of $F'_\xi/\xi^2,F/\xi^3$ has supremum at most $1/(2ws^2)$ and variation at most $3/(2ws^2)$: use the unimodality of $F/\xi$ or the one activation and thereafter decreasing $F'_\xi$, and then multiply by the decreasing reciprocal powers. Therefore the entire regular cost is at most $c_1/s+c_2/s^2$, where $c_1=5S_{a/2}/(2w)$ and $c_2=16/(2wt_s)$. For $V_{a/2}/t$ use supremum at most $1/t_s$ and variation at most $4/t_s$. These constants include both endpoints.

For $e>2d$, charge $c_1/\log 2+c_2/(\log2)^2$ times the square of the tapered mollifier mass. For $d<e\le2d$, put $h=e-d$. Then $s\ge h/(2d)$ and $\Omega(e)\le\Omega(d)$. At each $d$, the regular sum over this entire set of $h$ is at most
\[
 2c_1 d(1+\log X)+4d\sqrt{c_0c_2}.
\]
Use the elementary integral $\sum_{h\ge1}\min(c_0,4c_2d^2/h^2)\le\int_0^\infty\min(c_0,4c_2d^2/v^2)\,dv$. Sum the coefficient factor over $d$ with weight $d^{1-2\sigma}\Omega(d)^2$. Writing the taper square as an average of hard prefixes with measure $2\log(X/x)\,dx/(W^2x)$ on $[Y,X]$ allows the same certified periodic upper for the $d^{-a}$ power sum. The equality case $d=e$ costs only $c_0\zeta_q(2\sigma)$. Multiply by both absolute raw-index masses, without another mollifier factor, and by two for the two conjugate terms. Both orderings of the raw AFE indices remain included.

At $\alpha_0=64$ the [ordered cross-term verifier](quarter_ordered_cross.py) pays less than $84\,021\,674$ for the **entire interference with $d\le e$**, including all stationary boundary terms. The comparable cost at $\alpha_0=96$ is below $68\,601\,912$. Apply the earlier nonstationary estimate only to $d>e$ and to the subtracted forward constant. The constant lies in its outer region: $t_0=2\pi j/(qe)\ll t_s$ for every allowed $j$. With the earlier $4T$ forward cutoff and $\epsilon=.03$ the remaining signed allowance is above $1.0214455\,10^{10}$. The unresolved cross term now has $d>e$ and $|\log(t/t_0)|<.06$.

~~~powershell
python -B round8/critical/quarter_ordered_cross.py
~~~
